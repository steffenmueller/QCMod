SetLogFile("qc_C161.log");
_<x> := PolynomialRing(Rationals());
X :=  HyperellipticCurve( x^6+2*x^4+6*x^3+17*x^2+18*x+5 );

load "coleman.m";
load "symplectic_basis.m";
load "hecke_correspondence.m";
load "hodge.m";
load "frobenius.m";
load "heights.m";
load "qc_init_g2.m";




p := 29;      // prime number p
rho := 2;
N := 20; prec :=50; basis0 := []; basis1 := []; basis2 := []; 
printlevel := 2; debug := false; base_point := 0;




Q:=y^2 -( x^6+2*x^4+6*x^3+17*x^2+18*x+5 );

"Compute the rational points of the curve with affine model ",Q;
QQ := Rationals();
Qp := pAdicField(p,N);
r,Delta,s := auxpolys(Q);

pl := printlevel;


// ==========================================================
// ===               2) SYMPLECTIC BASIS                  ===
// ==========================================================
if pl gt 1 then print " Computing a symplectic basis of H^1"; end if;
  h1basis, g, r, W0 := h1_basis(Q,p,N);  
  if #basis0*#basis1 gt 0 then // Use the given basis
    h1basis := basis0 cat basis1;
  end if;
  if pl gt 1 then printf " genus = %o.\n", g; end if;
  if IsZero(rho) then 
    rho := g;       //If not given, we assume that the Picard number is equal to the genus
  end if;
  

  // h1basis is a basis of H^1 such that the first g elements span the regular
  // differentials. Construct a symplectic basis by changing the last g elements of h1basis.
  //
  standard_sympl_mat := ZeroMatrix(Rationals(),2*g,2*g);
  for i in [1..g] do
    standard_sympl_mat[i,g+i] := 1; standard_sympl_mat[g+i,i] := -1;
  end for;

  if pl gt 2 then print " Computing the cup product matrix"; end if;
  cpm_prec := 2*g;
  if assigned cpm then delete cpm; end if;
  repeat 
    try 
      //cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec := cpm_prec);
      cpm := cup_product_matrix_split_places(h1basis, Q, g, r, W0 : prec := cpm_prec);
    catch e;
      cpm_prec +:= g;
      if pl gt 3 then print "try again"; end if;
    end try;
  until assigned cpm;
  if pl gt 2 then print " Cup product matrix", cpm; end if;
  if cpm ne standard_sympl_mat then 
    coefficients := symplectic_basis(cpm); // Create coefficients of a symplectic basis in terms of h1basis
    new_complementary_basis := [&+[coefficients[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
    sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
    if not &and[&and[Valuation(c, p) ge 0 : c in Coefficients(w[1])] : w in sympl_basis] then
      error "The computed symplectic basis is not integral. Please try a different prime or a different basis.";
    end if; 
    if pl gt 2 then print " Symplectic basis of H^1", sympl_basis; end if;
    basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
    basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
  end if;
  data := coleman_data(Q,p,N : useU:=true,  basis0 := basis0, basis1 := basis1, basis2 := basis2);
data_hol := coleman_data(Q,p,5:useU:=false,basis0:=basis0,basis1:=basis1,basis2:=basis2);
if pl gt 1 then printf "Computed Coleman data at p=%o.\n", p; end if;

  prec := Max(100, tadicprec(data, 1));
  S    := LaurentSeriesRing(Qp,prec);

// ==========================================================
// ===                    POINTS                       ===
// ==========================================================
search_bound := 1000;
  Qpoints  := Q_points(data,search_bound); // small Q-rational points
  Nfactor := 1.5; // Additional precision for root finding in Qp_points
  computed_Qp_points := false;
  repeat 
    try 
      Qppoints := Qp_points(data : Nfactor := Nfactor); // One Q_p-point for every residue disk.
      computed_Qp_points := true;
    catch e; 
      Nfactor +:= 0.5;
    end try;
  until computed_Qp_points;

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
  // TODO: This might not always work for very bad points
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

  FF   := fun_field(data);
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
if pl gt 1 then printf "\n Computing correspondences";  end if;

  // Want rho-1 independent `nice` correspondences.
  // Construct them using powers of Hecke operator
  q := p;
  correspondences, Tq, corr_loss := hecke_corr(data,q,N : basis0:=basis0,basis1:=basis1,printlevel:=pl);

  Ncorr := N + Min(corr_loss, 0);
  // correspondences and Tq are provably correct to O(p^Ncorr), at least if q = p. We
  // represent them via rational approximations.
  //
  Qpcorr := pAdicField(p, Ncorr);
  mat_space := KMatrixSpace(Qpcorr, 2*g, 2*g);
  if pl gt 1 then printf "\nHecke operator at %o acting on H^1:\n%o\n", q, Tq; end if;
  if IsDiagonal(Tq) or Degree(CharacteristicPolynomial(Tq)) lt 2*g then
    error "p-Adic approximation of Hecke operator does not generate the endomorphism algebra. Please pick a different prime. ";
  end if;
  //if #nice_correspondences gt 0 then 
    //correspondences := nice_correspondences;
  //else
  
  // Check if Hecke operator generates. Need to do this using p-adic arithmetic.
  if Dimension(sub<mat_space | ChangeUniverse(correspondences, mat_space)>) lt rho-1 then
    error "Powers of Hecke operator don't suffice to generate the space of nice correspondences";
  end if;

  //end if;
    
  if pl gt 1 then printf "\n Nice correspondences:\n%o\n\n", correspondences; end if;

  Tq_small := ExtractBlock(Tq,1,1,g,g);                // Hecke operator at q on H^0(X,Omega^1)
  char_poly_Tq := CharacteristicPolynomial(Tq_small);  
  Qp_ext := quo<PolynomialRing(Qp) | char_poly_Tq>;
  Salpha := quo<PolynomialRing(S) | char_poly_Tq>;

  // Compute an End0(J)-equivariant splitting of the Hodge filtration.
  eqsplit := eq_split(Tq);


 // Test equivariance of splitting 
  big_split := BlockMatrix(1,2,[eqsplit,ZeroMatrix(Rationals(),2*g,g)]);
  check_equiv := ChangeRing((big_split*Transpose(Tq) - Transpose(Tq)*big_split), pAdicField(p, N-2));     
  min_val_check_equiv := Min([Min([Valuation(check_equiv[i,j]) : j in [1..g]]): i in [1..2*g]]);
  assert min_val_check_equiv ge N-3; 
  //assert IsZero(big_split*Transpose(Tq) - Transpose(Tq)*big_split);     // Test equivariance
  if pl gt 1 then printf "\n equivariant splitting:\n%o\n", eqsplit; end if;
  minvaleqsplit := minvalp(eqsplit, p);

  heights := [* *];    // heights of auxiliary points. Different correspondences allowed (might cut down the # of necessary rational pts).
  NE1E2Ps := Ncorr;  // Precision of E1 tensor E2 of auxiliary points
  Nhts := Ncorr; // Precision of local heights of auxiliary points
  Nexpansions := []; // Precision of power series expansion of local heights 
  c1s := [];
  E1P := 0;
  super_space := VectorSpace(Qp, g+1);
  E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
  E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
  E1_E2_P_vectors := [ ];  // E1 tensor E2 of auxiliary points and away coeffs


Z := correspondences[1];

// ==========================================================
// ===                     HODGE                       ===
// ==========================================================
if pl gt 0 then printf  " Computing Hodge filtration\n"; end if;

if assigned betafil then delete betafil; end if;
hodge_prec := 5; 
repeat
  try
    eta,betafil,gammafil,hodge_loss := hodge_data(data,Z,bpt: prec := hodge_prec);
  catch e;
    hodge_prec +:= 5;
  end try;
until assigned betafil;

Nhodge := Ncorr + Min(0, hodge_loss);

if pl gt 1 then 
  printf  " eta =  %o.\n", eta; 
  printf  " beta_fil  =  %o.\n", betafil; 
  printf  " gamma_fil =  %o.\n\n", gammafil; 
end if;

valeta := 0;
valbetafil := minvalp(betafil, p);
maxdeggammafil := Max([Degree(a) : a in Eltseq(gammafil)]);
minvalgammafil :=  
    Min([Min([0] cat [Valuation(c, p) : c in Coefficients(a)]) : a in Eltseq(gammafil)]);


// ==========================================================
// ===                  FROBENIUS                      ===
// ==========================================================
b0 := teichmueller_pt(bQ,data); 
if pl gt 0 then printf  " Computing Frobenius structure.\n"; end if;
b0pt := [QQ!c : c in xy_coordinates(b0, data)]; // xy-coordinates of P
//G, NG, valc := frob_struc(data,Z,eta,b0pt); 
G, NG := frob_struc(data,Z,eta,b0pt : N:=Nhodge); 
G_list := [**]; // evaluations of G at Teichmuellers of all good points (0 if bad)
for i := 1 to numberofpoints do
  if is_bad(Qppoints[i],data) then
    G_list[i]:=0;
  else
    P  := teichpoints[i]; // P is the Teichmueller point in this disk
    pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
    G_list[i] := eval_mat_R(G,pt,r); // P is finite good, so no precision loss. 
  end if;
end for;
Ncurrent := Min(Nhodge, NG);
//"Nhodge, NG", Nhodge, NG;

PhiAZb_to_b0, Nptb0 := parallel_transport(bQ,b0,Z,eta,data:prec:=prec,N:=Nhodge);
for i := 1 to 2*g do
  PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
end for;

PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)

Ncurrent := Min(Ncurrent, Nptb0);
Nfrob_equiv_iso := Ncurrent;
minvalPhiAZbs := [0 : i in [1..numberofpoints]];
for i := 1 to numberofpoints do

  if G_list[i] eq 0 then
    PhiAZb[i] := 0;
  else 
    pti, Npti := parallel_transport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge);
    isoi, Nisoi := frob_equiv_iso(G_list[i],data,Ncurrent);
    MNi := Npti lt Nisoi select Parent(pti) else Parent(isoi);
    PhiAZb[i] := MNi!(pti*PhiAZb_to_b0*isoi);
    Nfrob_equiv_iso := Min(Nfrob_equiv_iso, minprec(PhiAZb[i]));
    minvalPhiAZbs[i] := minval(PhiAZb[i]);
  end if;
end for;
Ncurrent := Nfrob_equiv_iso;
c1 := Min(minvalPhiAZbs); 

PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
    parallel_transport_to_z(Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge)*PhiAZb[i]; 
end for;
 

gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 
if pl gt 2 then printf  "Computing expansions of the filtration-respecting function gamma_fil.\n"; end if;
for i := 1 to numberofpoints do
  if G_list[i] ne 0 then
    gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, Nhodge, prec);
  end if;
end for;


// ==========================================================
// ===                  HEIGHTS                        ===
// ==========================================================
   


// We know that local heights away from p can only be trivial at 2. We also know
// that there is some c of the form rational*log(2) such that h_2(P) = c*f(P), where f(P) is 0,1 or 2
// depending on whether v_2(x(P)) is 0, <2 or >2. So we record f(P) for the known rational
// points (not the base point to avoid index problems).
factors_away_known_rat_points := [0, -1,-1,1,1,0,0];
all_factors_away := [0,-1,1];

// Idea: We solve for a1, a2 and c such that
// h = a1*psi1 + a2*psi2, where psi1 and psi2 is the dual of the E1_tensor_E2-basis of
// suitable rational points.
// To do so, we compute h_p(P), E1(P) and E2(P) for sufficiently many known rational points (we need 3)
// and solve a linear system.
//



 // First find a point with non-zero E1 to write down a basis of the Lie algebra. 
// To minimize precision loss, want small valuation of
// determinant of change of basis matrix.
min_val_det_i := Ncurrent;
for i := 1 to #good_affine_rat_pts_xy_no_bpt do
  Qpti := i lt global_base_point_index select good_Qpoints[i]
                      else good_Qpoints[i+1];
  pti, Npti := parallel_transport(Qppoints[ks[i]], Qpti, Z,eta,data:prec:=prec,N:=Nhodge);
  
  MNi := Npti lt Precision(BaseRing(PhiAZb[ks[i]])) select Parent(pti) else Parent(PhiAZb[ks[i]]);
  PhiP := MNi!(pti*PhiAZb[ks[i]]);
  E1Pi := Vector(BaseRing(PhiP),g,[PhiP[j+1,1] : j in [1..g]]);
  NE1Pi := Min([Ncurrent, minprec(E1Pi)]);

  basisH0star_i := [];
  for i := 0 to g-1 do
    // basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P)
    Append(~basisH0star_i, Eltseq(E1Pi*(ChangeRing(Tq_small,BaseRing(E1Pi))^i))); 
  end for; 
  val_det_i := Valuation(Determinant(Matrix(basisH0star_i)));
  if val_det_i lt min_val_det_i then
    // Better point found
    min_val_det_i := val_det_i; min_i := i; 
    E1P := E1Pi; NH0star := NE1Pi;
    basisH0star := basisH0star_i;
  end if;
  if IsZero(val_det_i) then break; end if;
end for;
if min_val_det_i ge Ncurrent then  // precision loss too high to obtain meaningful result.
  error "No good basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P) found";
end if;
changebasis:=Matrix(basisH0star)^(-1);
minvalchangebasis := minval(changebasis);
if pl gt 1 then 
  printf " Using point %o to generate.\n", 
                            good_affine_rat_pts_xy_no_bpt[min_i]; 
end if;



// heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  Qpti := i lt global_base_point_index select good_Qpoints[i]
              else good_Qpoints[i+1];

  pti, Npti := parallel_transport(Qppoints[ks[i]], Qpti, Z,eta,data:prec:=prec,N:=Nhodge);
  MNi := Npti lt Precision(BaseRing(PhiAZb[ks[i]])) select Parent(pti) else Parent(PhiAZb[ks[i]]);
  PhiP := MNi!(pti*PhiAZb[ks[i]]);
  E1Pi := Vector(BaseRing(PhiP),g,[PhiP[j+1,1] : j in [1..g]]);
  Phii := MNi!(pti*PhiAZb[ks[i]]);
  Ni := Min([Ncurrent, Precision(BaseRing(Phii)), minprec(Phii)]);
  Qpi := pAdicField(p, Ni);
  Qpix := PolynomialRing(Qpi);
  Qp_ext := quo< Qpix | Qpix!char_poly_Tq>;
  E1_E2_P:= E1_tensor_E2(Phii,betafil,changebasis,data,Qp_ext);
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_away_known_rat_points[i]);  // don't forget about local height at 2
  NE1E2P := Min(Ni,minprec(E1_E2_P));
  NLA := Integers()!Min(Precision(BaseRing(E1_E2_subspace)), NE1E2P);
  // p^NLA is the precision for the linear algebra computation.
  new_super_space := VectorSpace(pAdicField(p, NLA), g+1);
  old_basis := ChangeUniverse(Basis(E1_E2_subspace), new_super_space); 
  new_E1_E2_subspace := sub<new_super_space | old_basis cat [new_super_space!Eltseq(E1_E2_P_vector)]>;
  if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
    E1_E2_subspace := new_E1_E2_subspace; 
    if pl gt 1 then printf " Using point %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i]; end if;

    gammafilP := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qpti,data);
    height_P := height(Phii,betafil,gammafilP,eqsplit,data);
    NhtP := AbsolutePrecision(height_P); 
    Append(~heights, height_P); // height of A_Z(b, P)
    Append(~E1_E2_Ps, E1_E2_P);
    Append(~E1_E2_P_vectors, E1_E2_P_vector);
    Nhts := Min(Nhts, NhtP);
    NE1E2Ps := Min(NE1E2Ps, NE1E2P);
  end if;
  i +:= 1;
until #heights eq g+1 or i gt #ks; 


/*
// local_heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  loc_coord := - Qppoints[ks[i]]`x + good_affine_rat_pts_xy_no_bpt[i][1];
  // local coordinate of the ith known ratl pt P
  E1_E2_series := E1_tensor_E2(PhiAZb_to_z[ks[i]],betafil,basisH0star,data,Salpha);
  Kt := Parent(E1_E2_series);
  E1_E2_P := Qp_ext![Evaluate(c, loc_coord) : c in Eltseq(E1_E2_series)];
  
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_away_known_rat_points[i]);  // don't forget about height at 2
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
until #local_heights eq g+1 or i gt #ks; */


local_height_list := [*0 : k in [1..numberofpoints]*];
E1_E2_list := [*0 : k in [1..numberofpoints]*];
for k := 1 to numberofpoints do
  if G_list[k] ne 0 then

    local_height_list[k] := height(PhiAZb_to_z[k],betafil,gammafil_listb_to_z[k],eqsplit,data);
          E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,changebasis,data,Salpha);

  end if;
end for;  // k := 1 to numberofpoints 
   
assert #heights eq g+1;

// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. Also solve for h2-constant c
//
E1_E2_Ps_matrix := Matrix(pAdicField(p, NE1E2Ps), [Eltseq(E1_E2) : E1_E2 in E1_E2_P_vectors]);
mat := E1_E2_Ps_matrix^(-1) ;
matprec := minprec(mat);

Qpht := pAdicField(p, Min([matprec, NE1E2Ps, Nhts]));
heights_vector := Matrix(Qpht, g+1,1, [ht : ht in heights]);
height_coeffs := ChangeRing(mat, Qpht)*heights_vector;

c := height_coeffs[3,1];
//printf "local heights at %o are multiples of %o*log(7)\n", 7, lindepQp(c/Log(pAdicField(p,N-2)!7));

away_contributions := [a*c : a in all_factors_away];
"away_contributions", away_contributions ;
// so the global height is of the form sum_i height_coeffs[i]*Psi[i], where 
// Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)
//
Nhtcoeffs := minprec(height_coeffs); // Precision of height_coeffs
c3 := minval(height_coeffs);
min_root_prec := N;  // smallest precision of roots of QC function

F_list := [**];
for l := 1 to numberofpoints do
  if G_list[l] eq 0 then
    F_list[l] := 0;
  else
    // now find the locally analytic function that extends the global height.
    global_height := &+[height_coeffs[j,1]*Eltseq(E1_E2_list[l])[j] : j in [1..g]];
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
 
c2 := Min([0, valbetafil, minvaleqsplit, valbetafil+ minvaleqsplit]); 
     
i0 := 0;
i0_threshold := Min([valeta, valbetafil/2, (minvalgammafil-c2)/2]);
repeat 
  i0 +:= 1;
until -Floor(log(p,i0)) le i0_threshold;

function valF(i) 
  // lower bound on valuations of coefficients in entries of F_list
  assert i ge i0;
  valgammafili := i le maxdeggammafil select minvalgammafil else 0;
  return -2*Floor(log(p,i)) +c1 + Min(c2,c3+2*minvalchangebasis);
end function;


/*
// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. Also solve for h2-constant c
E1_E2_Ps_matrix := Matrix(E1_E2_P_vectors);
local_heights_vector := Matrix(g+1,1,[ht : ht in local_heights]);
height_coeffs := Eltseq(E1_E2_Ps_matrix^(-1)*local_heights_vector);

c := height_coeffs[3];
//printf "local heights at %o are multiples of %o*log(7)\n", 7, lindepQp(c/Log(pAdicField(p,N-2)!7));

away_contributions := [a*c : a in all_factors_away];
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
 */

zero_list := [* *];
sol_list  := [* *];
Nend := Integers()!Min(Ncurrent, Nhtcoeffs); // Precision used for root finding 

if pl gt 0 then
  printf " The quadratic Chabauty function is correct to precision %o^%o.\n",  p, Nend;
end if;
Qp_small   := pAdicField(p,Nend); 
Qptt := PowerSeriesRing(Qp_small,prec);
Zp_small   := pAdicRing(p,Nend);
Zpt  := PolynomialRing(Zp_small);
Qpt  := PolynomialRing(Qp_small);

// ==========================================================
// ===                    FIND ZEROES                     ===
// ==========================================================

for i := 1 to numberofpoints do
  sol_list[i] := []; 
  zero_list[i] := []; 
  if F_list[i] ne 0 then
    Pp := Qppoints[i];
    xt, bt := local_coord(Pp,prec,data);
    W0invxt := Evaluate(W0^(-1), xt);
    b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
    yt := &+[W0invxt[2,j]*b_vector[j,1] : j in [1..Degree(Q)]];
    if not &and[Valuation(Coefficient(F_list[i],j)) - valF(j) 
                      ge 0 : j in [i0..Degree(F_list[i])]] then
      error "Valuations of coefficients violate lower bound,
          so the quadratic Chabauty function cannot be correct. 
            This is a bug -- please report!"; 
    end if;

    for contrib in away_contributions do
      // solve F_list[i] = contrib 
      f := Evaluate(Qptt!(F_list[i]-contrib),p*Qptt.1);
      precf := Precision(f)[1];
      // Compute roots of f(t) = F(pt)
      bound_val_coeffs_f := valF(precf) + precf;
      if bound_val_coeffs_f lt N then  // Lemma 4.7
        error "TODO: Lower p-adic precision if t-adic prec is too small";
      end if;
      roots, root_prec, f := roots_with_prec(f, Nend);

      if not IsEmpty(roots) then
        roots_precs := [root_prec];
        if #roots gt 1 then 
          // Recenter and rescale so that there is precisely one root
          // in the unit ball
          sep_ints := separate([rt[1] : rt in roots]);
          // sep_int[i] is the smallest n such that roots[i] is distinct
          // from the other roots modulo p^n
          for j := 1 to #roots do
            r := roots[j,1];
            // move r to 0
            f_shifted :=Evaluate(f, Qptt.1+r);
            // new_f = f(p^(s+1)*(t+r)), s  = sep_ints[j]
            new_f:= Evaluate(f_shifted, p^(1+sep_ints[j])*Qptt.1);
            precnewf := Precision(new_f)[1];
            bound_val_coeffs_new_f := precnewf*(sep_ints[j]+1) + valF(precnewf);        
            
            if bound_val_coeffs_new_f lt N then  // Lemma 4.7
              error "TODO: Lower p-adic precision if t-adic prec is too small";
            end if;
            // Compute roots of f(p^(s+1)*(t+r))
            new_roots, new_root_prec := roots_with_prec(new_f, Nend);
            // check that there is only one root. otherwise there's a bug.
            assert #new_roots eq 1; 
            // if the shifted and scaled root isn't quite zero, decrease precision
            // accordingly.
            new_root_prec := Min(new_root_prec, Valuation(new_roots[1,1]));
            roots_precs[j] := Max(new_root_prec+sep_ints[j]+1, root_prec);
            min_root_prec := Min(min_root_prec, roots_precs[j]);
            // minimal precision to which a root of F is known.
          end for;
        else 
          min_root_prec := Min(min_root_prec, root_prec);
        end if; // #roots gt 1

        known := false;
        for j := 1 to #roots do
          r := roots[j,1];
          ChangePrecision(~roots[j,1], roots_precs[j]);  // Lemma 4.7
          // p*r is correct to roots_precs[j]+1 digits
          Qproot := pAdicField(p, roots_precs[j] + 1); 
          // So pt is provably correct to the precision of Qproot
          pt := [Qproot!Evaluate(c, p*r) : c in [xt, yt]];
          for k := 1 to #sol_list do 
            // Check if this solution is already known
            if #sol_list[k] gt 0 then 
              for l := 1 to #sol_list[k] do
                sol := sol_list[k,l,1];
                if are_congruent(pt, sol) then
                  // pt already known -> multiple root
                  sol_list[k,l,2] := true;
                  known := true;
                end if;
              end for;
            end if;
          end for; // k := 1 to #sol_list do 
          if not known then
            if roots[j][2] le 0 then  // TODO: want <= root_prec??
              Append(~sol_list[i], <pt, true>); // multiple root
            else 
              Append(~sol_list[i], <pt, false>); // simple root
            end if;
          end if;
        end for; // j:=1 to #roots
      end if; // not IsEmpty(roots)
      zero_list[i] := roots;

    end for; // contrib in away_contributions
  end if; // F_list[i] ne 0
end for;  // i:=1 to numberofpoints

if pl gt 0 then
  printf " All roots of the quadratic Chabauty function(s) are correct to precision at least %o^%o.\n", p, min_root_prec;
end if;

// ==========================================================
// ===                    SANITY CHECK                    ===
// ==========================================================

/*
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
    if pl gt 2 then  print good_affine_rat_pts_xy[j], "Valuation of the quadratic Chabauty function minus sum of contributions away from p", vals; end if;
    assert exists(v){ val : val in vals | val ge Nend/2};
  count := count+1;
  end if;
end for;
"Sanity check passed";
*/


K := pAdicField(p, min_root_prec);
fake_rat_pts := [* *]; 
recovered_rat_pts_count := 0;
number_of_known_rat_pts := #good_affine_rat_pts_xy;
sols := &cat[L : L in sol_list | #L gt 0];
for i := 1 to #sols do
//    P := [lindepQp(sols[i,1]), lindepQp(sols[i,2])];
  known_rational := false;
  sol := sols[i,1];
  multiple := sols[i,2];
  for pt in good_affine_rat_pts_xy do
    // Check if sols is congruent to a known rational point
    if are_congruent(sols[i,1], pt) then
    //if IsZero(K!sols[i,1] - K!pt[1]) and IsZero (K!sols[i,2] - K!pt[2]) then
      if pl gt 1 then " Recovered known rational point", pt; end if;
      if multiple then 
        error "Multiple root at rational point. Try increasing p-adic precision (parameter N).";
      end if;
      known_rational := true;
      recovered_rat_pts_count +:= 1;
      break;
    end if;
  end for;
  if not known_rational then
    P := [lindepQp(K!sols[i,1,1]), lindepQp(K!sols[i,1,2])];
    //if pl gt 0 then printf "Rational reconstruction of point %o is \%o ", i,P; end if;
    if IsZero(eval_Q(Q, P[1], P[2])) then
      if pl gt 1 then " Found unknown rational point P", P; end if;
      if multiple then 
        error "Multiple root at rational point. Try increasing p-adic precision (parameter N).";
      end if;
      Append(~good_affine_rat_pts_xy, P); 
    else 
      Append(~fake_rat_pts, sols[i,1]); 
      if pl gt 1 then 
        printf " Solution %o does not seem to be rational.\n", sols[i,1]; 
      end if;
      // Here multiple roots are fine.
    end if;
  end if;
end for;
if number_of_known_rat_pts gt recovered_rat_pts_count then
  error "Not all known rational points in good disks where recovered.";
end if;


fake_rat_pts_affine := fake_rat_pts;
good_rat_pts_affine := good_affine_rat_pts_xy;
 

"";
"Run the Mordell-Weil sieve to show there are no additional rational points in affine disks.";

base_pt := [1/4,209/64];
J := Jacobian(X);
torsion_bas, torsion_orders, bas := generators(J);
assert #bas eq 2; // rank = 2
divisors := [* [* [[-1,1]],[[1,7]]*],    [* [[1/2,-35/2^3]], [[1/4,209/4^3]] *]*];
P1 := X![-1,1]-X![1,7];
P2 := X![1,-35,2]-X![1,209,4];

splitting_generators := [P1,P2];
"Use independent points", splitting_generators;
splitting_indices := [[0,-1], [-5,-4]];
fake_coeffs_mod_pN, rat_coeffs_mod_pN := coefficients_mod_pN(fake_rat_pts_affine, good_rat_pts_affine, divisors, base_pt, splitting_indices, data_hol); 
// We only consider the affine points here, because there's a convergence issue at infinity.
fake_coeffs := [* *];
Append(~fake_coeffs, [ fake_coeffs_mod_pN ]);
mws_primes := [199,373,463];

qc_M := p^3;
M := qc_M;
qc_fake_coeffs_mod_M := coeffs_CRT(fake_coeffs, [p], [3]);

n := 4;
printf "adding information mod n=%o\n", n;
time fake_coeffs_mod_M := combine_fake_good(qc_fake_coeffs_mod_M, M, n);
M := qc_M*n; // modulus
"number of cosets", #fake_coeffs_mod_M;

"Start the Mordell-Weil sieve";
time done_fake := MWSieve(J, mws_primes, M, bas cat torsion_bas, X!base_pt, fake_coeffs_mod_M : known_rat_coeffs := rat_coeffs_mod_pN );

"done with the Mordell-Weil sieve?", done_fake;
"For sieving used the prime(s)", mws_primes;



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
base_point := [4,209];
QQ := Rationals();
Qp := pAdicField(p,N);
r,Delta,s := auxpolys(Q);
// ==========================================================
// ===               2) SYMPLECTIC BASIS                  ===
// ==========================================================
if pl gt 1 then print " Computing a symplectic basis of H^1"; end if;
  h1basis, g, r, W0 := h1_basis(Q,p,N);  
  if pl gt 1 then printf " genus = %o.\n", g; end if;
  if IsZero(rho) then 
    rho := g;       //If not given, we assume that the Picard number is equal to the genus
  end if;
  

  // h1basis is a basis of H^1 such that the first g elements span the regular
  // differentials. Construct a symplectic basis by changing the last g elements of h1basis.
  //
  standard_sympl_mat := ZeroMatrix(Rationals(),2*g,2*g);
  for i in [1..g] do
    standard_sympl_mat[i,g+i] := 1; standard_sympl_mat[g+i,i] := -1;
  end for;

  if pl gt 2 then print " Computing the cup product matrix"; end if;
  cpm_prec := 2*g;
  if assigned cpm then delete cpm; end if;
  repeat 
    try 
      //cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec := cpm_prec);
      cpm := cup_product_matrix_split_places(h1basis, Q, g, r, W0 : prec := cpm_prec);
    catch e;
      cpm_prec +:= g;
      if pl gt 3 then print "try again"; end if;
    end try;
  until assigned cpm;
  if pl gt 2 then print " Cup product matrix", cpm; end if;
  if cpm ne standard_sympl_mat then 
    coefficients := symplectic_basis(cpm); // Create coefficients of a symplectic basis in terms of h1basis
    new_complementary_basis := [&+[coefficients[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
    sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
    if not &and[&and[Valuation(c, p) ge 0 : c in Coefficients(w[1])] : w in sympl_basis] then
      error "The computed symplectic basis is not integral. Please try a different prime or a different basis.";
    end if; 
    if pl gt 2 then print " Symplectic basis of H^1", sympl_basis; end if;
    basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
    basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
  end if;
  data := coleman_data(Q,p,N : useU:=true,  basis0 := basis0, basis1 := basis1, basis2 := basis2);
data_hol_inf := coleman_data(Q,p,13:useU:=false,basis0:=basis0,basis1:=basis1,basis2:=basis2);
if pl gt 1 then printf "Computed Coleman data at p=%o.\n", p; end if;

  prec := Max(100, tadicprec(data, 1));
  S    := LaurentSeriesRing(Qp,prec);

// ==========================================================
// ===                    POINTS                       ===
// ==========================================================
search_bound := 1000;
Qpoints  := Q_points(data,search_bound); // small Q-rational points
Nfactor := 1.5; // Additional precision for root finding in Qp_points
computed_Qp_points := false;
repeat 
  try 
    Qppoints := Qp_points(data : Nfactor := Nfactor); // One Q_p-point for every residue disk.
    computed_Qp_points := true;
  catch e; 
    Nfactor +:= 0.5;
  end try;
until computed_Qp_points;

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
// TODO: This might not always work for very bad points
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

FF   := fun_field(data);
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
if pl gt 1 then printf "\n Computing correspondences";  end if;

  // Want rho-1 independent `nice` correspondences.
  // Construct them using powers of Hecke operator
  q := p;
  correspondences, Tq, corr_loss := hecke_corr(data,q,N : basis0:=basis0,basis1:=basis1,printlevel:=pl);

  Ncorr := N + Min(corr_loss, 0);
  // correspondences and Tq are provably correct to O(p^Ncorr), at least if q = p. We
  // represent them via rational approximations.
  //
  Qpcorr := pAdicField(p, Ncorr);
  mat_space := KMatrixSpace(Qpcorr, 2*g, 2*g);
  if pl gt 1 then printf "\nHecke operator at %o acting on H^1:\n%o\n", q, Tq; end if;
  if IsDiagonal(Tq) or Degree(CharacteristicPolynomial(Tq)) lt 2*g then
    error "p-Adic approximation of Hecke operator does not generate the endomorphism algebra. Please pick a different prime. ";
  end if;
  //if #nice_correspondences gt 0 then 
    //correspondences := nice_correspondences;
  //else
  
  // Check if Hecke operator generates. Need to do this using p-adic arithmetic.
  if Dimension(sub<mat_space | ChangeUniverse(correspondences, mat_space)>) lt rho-1 then
    error "Powers of Hecke operator don't suffice to generate the space of nice correspondences";
  end if;

  //end if;
    
  if pl gt 1 then printf "\n Nice correspondences:\n%o\n\n", correspondences; end if;

  Tq_small := ExtractBlock(Tq,1,1,g,g);                // Hecke operator at q on H^0(X,Omega^1)
  char_poly_Tq := CharacteristicPolynomial(Tq_small);  
  Qp_ext := quo<PolynomialRing(Qp) | char_poly_Tq>;
  Salpha := quo<PolynomialRing(S) | char_poly_Tq>;

  // Compute an End0(J)-equivariant splitting of the Hodge filtration.
  eqsplit := eq_split(Tq);


 // Test equivariance of splitting 
  big_split := BlockMatrix(1,2,[eqsplit,ZeroMatrix(Rationals(),2*g,g)]);
  check_equiv := ChangeRing((big_split*Transpose(Tq) - Transpose(Tq)*big_split), pAdicField(p, N-2));     
  min_val_check_equiv := Min([Min([Valuation(check_equiv[i,j]) : j in [1..g]]): i in [1..2*g]]);
  assert min_val_check_equiv ge N-3; 
  //assert IsZero(big_split*Transpose(Tq) - Transpose(Tq)*big_split);     // Test equivariance
  if pl gt 1 then printf "\n equivariant splitting:\n%o\n", eqsplit; end if;
  minvaleqsplit := minvalp(eqsplit, p);

  heights := [* *];    // heights of auxiliary points. Different correspondences allowed (might cut down the # of necessary rational pts).
  NE1E2Ps := Ncorr;  // Precision of E1 tensor E2 of auxiliary points
  Nhts := Ncorr; // Precision of local heights of auxiliary points
  Nexpansions := []; // Precision of power series expansion of local heights 
  c1s := [];
  E1P := 0;
  super_space := VectorSpace(Qp, g+1);
  E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
  E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
  E1_E2_P_vectors := [ ];  // E1 tensor E2 of auxiliary points and away coeffs


Z := correspondences[1];

// ==========================================================
// ===                     HODGE                       ===
// ==========================================================
if pl gt 0 then printf  " Computing Hodge filtration\n"; end if;

if assigned betafil then delete betafil; end if;
hodge_prec := 5; 
repeat
  try
    eta,betafil,gammafil,hodge_loss := hodge_data(data,Z,bpt: prec := hodge_prec);
  catch e;
    hodge_prec +:= 5;
  end try;
until assigned betafil;

Nhodge := Ncorr + Min(0, hodge_loss);

if pl gt 1 then 
  printf  " eta =  %o.\n", eta; 
  printf  " beta_fil  =  %o.\n", betafil; 
  printf  " gamma_fil =  %o.\n\n", gammafil; 
end if;

valeta := 0;
valbetafil := minvalp(betafil, p);
maxdeggammafil := Max([Degree(a) : a in Eltseq(gammafil)]);
minvalgammafil :=  
    Min([Min([0] cat [Valuation(c, p) : c in Coefficients(a)]) : a in Eltseq(gammafil)]);


// ==========================================================
// ===                  FROBENIUS                      ===
// ==========================================================
b0 := teichmueller_pt(bQ,data); 
if pl gt 0 then printf  " Computing Frobenius structure.\n"; end if;
b0pt := [QQ!c : c in xy_coordinates(b0, data)]; // xy-coordinates of P
//G, NG, valc := frob_struc(data,Z,eta,b0pt); 
G, NG := frob_struc(data,Z,eta,b0pt : N:=Nhodge); 
G_list := [**]; // evaluations of G at Teichmuellers of all good points (0 if bad)
for i := 1 to numberofpoints do
  if is_bad(Qppoints[i],data) then
    G_list[i]:=0;
  else
    P  := teichpoints[i]; // P is the Teichmueller point in this disk
    pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
    G_list[i] := eval_mat_R(G,pt,r); // P is finite good, so no precision loss. 
  end if;
end for;
Ncurrent := Min(Nhodge, NG);
//"Nhodge, NG", Nhodge, NG;

PhiAZb_to_b0, Nptb0 := parallel_transport(bQ,b0,Z,eta,data:prec:=prec,N:=Nhodge);
for i := 1 to 2*g do
  PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
end for;

PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)

Ncurrent := Min(Ncurrent, Nptb0);
Nfrob_equiv_iso := Ncurrent;
minvalPhiAZbs := [0 : i in [1..numberofpoints]];
for i := 1 to numberofpoints do

  if G_list[i] eq 0 then
    PhiAZb[i] := 0;
  else 
    pti, Npti := parallel_transport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge);
    isoi, Nisoi := frob_equiv_iso(G_list[i],data,Ncurrent);
    MNi := Npti lt Nisoi select Parent(pti) else Parent(isoi);
    PhiAZb[i] := MNi!(pti*PhiAZb_to_b0*isoi);
    Nfrob_equiv_iso := Min(Nfrob_equiv_iso, minprec(PhiAZb[i]));
    minvalPhiAZbs[i] := minval(PhiAZb[i]);
  end if;
end for;
Ncurrent := Nfrob_equiv_iso;
c1 := Min(minvalPhiAZbs); 

PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
for i := 1 to numberofpoints do
  PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
    parallel_transport_to_z(Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge)*PhiAZb[i]; 
end for;
 

gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 
if pl gt 2 then printf  "Computing expansions of the filtration-respecting function gamma_fil.\n"; end if;
for i := 1 to numberofpoints do
  if G_list[i] ne 0 then
    gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, Nhodge, prec);
  end if;
end for;


// ==========================================================
// ===                  HEIGHTS                        ===
// ==========================================================
   


// We know that local heights away from p can only be trivial at 2. We also know
// that there is some c of the form rational*log(2) such that h_2(P) = c*f(P), where f(P) is 0,1 or 2
// depending on whether v_2(x(P)) is 0, <2 or >2. So we record f(P) for the known rational
// points (not the base point to avoid index problems).
factors_away_known_rat_points := [0,0,0,0,0,-1,-1,1,1];
all_factors_away := [0,-1,1];

// Idea: We solve for a1, a2 and c such that
// h = a1*psi1 + a2*psi2, where psi1 and psi2 is the dual of the E1_tensor_E2-basis of
// suitable rational points.
// To do so, we compute h_p(P), E1(P) and E2(P) for sufficiently many known rational points (we need 3)
// and solve a linear system.
//



 // First find a point with non-zero E1 to write down a basis of the Lie algebra. 
// To minimize precision loss, want small valuation of
// determinant of change of basis matrix.
min_val_det_i := Ncurrent;
for i := 1 to #good_affine_rat_pts_xy_no_bpt do
  Qpti := i lt global_base_point_index select good_Qpoints[i]
                      else good_Qpoints[i+1];
  pti, Npti := parallel_transport(Qppoints[ks[i]], Qpti, Z,eta,data:prec:=prec,N:=Nhodge);
  
  MNi := Npti lt Precision(BaseRing(PhiAZb[ks[i]])) select Parent(pti) else Parent(PhiAZb[ks[i]]);
  PhiP := MNi!(pti*PhiAZb[ks[i]]);
  E1Pi := Vector(BaseRing(PhiP),g,[PhiP[j+1,1] : j in [1..g]]);
  NE1Pi := Min([Ncurrent, minprec(E1Pi)]);

  basisH0star_i := [];
  for i := 0 to g-1 do
    // basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P)
    Append(~basisH0star_i, Eltseq(E1Pi*(ChangeRing(Tq_small,BaseRing(E1Pi))^i))); 
  end for; 
  val_det_i := Valuation(Determinant(Matrix(basisH0star_i)));
  if val_det_i lt min_val_det_i then
    // Better point found
    min_val_det_i := val_det_i; min_i := i; 
    E1P := E1Pi; NH0star := NE1Pi;
    basisH0star := basisH0star_i;
  end if;
  if IsZero(val_det_i) then break; end if;
end for;
if min_val_det_i ge Ncurrent then  // precision loss too high to obtain meaningful result.
  error "No good basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P) found";
end if;
changebasis:=Matrix(basisH0star)^(-1);
minvalchangebasis := minval(changebasis);
if pl gt 1 then 
  printf " Using point %o to generate.\n", 
                            good_affine_rat_pts_xy_no_bpt[min_i]; 
end if;



// heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  Qpti := i lt global_base_point_index select good_Qpoints[i]
              else good_Qpoints[i+1];

  pti, Npti := parallel_transport(Qppoints[ks[i]], Qpti, Z,eta,data:prec:=prec,N:=Nhodge);
  MNi := Npti lt Precision(BaseRing(PhiAZb[ks[i]])) select Parent(pti) else Parent(PhiAZb[ks[i]]);
  PhiP := MNi!(pti*PhiAZb[ks[i]]);
  E1Pi := Vector(BaseRing(PhiP),g,[PhiP[j+1,1] : j in [1..g]]);
  Phii := MNi!(pti*PhiAZb[ks[i]]);
  Ni := Min([Ncurrent, Precision(BaseRing(Phii)), minprec(Phii)]);
  Qpi := pAdicField(p, Ni);
  Qpix := PolynomialRing(Qpi);
  Qp_ext := quo< Qpix | Qpix!char_poly_Tq>;
  E1_E2_P:= E1_tensor_E2(Phii,betafil,changebasis,data,Qp_ext);
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_away_known_rat_points[i]);  // don't forget about local height at 2
  NE1E2P := Min(Ni,minprec(E1_E2_P));
  NLA := Integers()!Min(Precision(BaseRing(E1_E2_subspace)), NE1E2P);
  // p^NLA is the precision for the linear algebra computation.
  new_super_space := VectorSpace(pAdicField(p, NLA), g+1);
  old_basis := ChangeUniverse(Basis(E1_E2_subspace), new_super_space); 
  new_E1_E2_subspace := sub<new_super_space | old_basis cat [new_super_space!Eltseq(E1_E2_P_vector)]>;
  if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
    E1_E2_subspace := new_E1_E2_subspace; 
    if pl gt 1 then printf " Using point %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i]; end if;

    gammafilP := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qpti,data);
    height_P := height(Phii,betafil,gammafilP,eqsplit,data);
    NhtP := AbsolutePrecision(height_P); 
    Append(~heights, height_P); // height of A_Z(b, P)
    Append(~E1_E2_Ps, E1_E2_P);
    Append(~E1_E2_P_vectors, E1_E2_P_vector);
    Nhts := Min(Nhts, NhtP);
    NE1E2Ps := Min(NE1E2Ps, NE1E2P);
  end if;
  i +:= 1;
until #heights eq g+1 or i gt #ks; 


/*
// local_heights contains the list of local heights of auxiliary points
i := 1;
repeat 
  loc_coord := - Qppoints[ks[i]]`x + good_affine_rat_pts_xy_no_bpt[i][1];
  // local coordinate of the ith known ratl pt P
  E1_E2_series := E1_tensor_E2(PhiAZb_to_z[ks[i]],betafil,basisH0star,data,Salpha);
  Kt := Parent(E1_E2_series);
  E1_E2_P := Qp_ext![Evaluate(c, loc_coord) : c in Eltseq(E1_E2_series)];
  
  E1_E2_P_vector := Append(Eltseq(E1_E2_P), -factors_away_known_rat_points[i]);  // don't forget about height at 2
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
until #local_heights eq g+1 or i gt #ks; */


local_height_list := [*0 : k in [1..numberofpoints]*];
E1_E2_list := [*0 : k in [1..numberofpoints]*];
for k := 1 to numberofpoints do
  if G_list[k] ne 0 then

    local_height_list[k] := height(PhiAZb_to_z[k],betafil,gammafil_listb_to_z[k],eqsplit,data);
          E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,changebasis,data,Salpha);

  end if;
end for;  // k := 1 to numberofpoints 
   
assert #heights eq g+1;

// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. Also solve for h2-constant c
//
E1_E2_Ps_matrix := Matrix(pAdicField(p, NE1E2Ps), [Eltseq(E1_E2) : E1_E2 in E1_E2_P_vectors]);
mat := E1_E2_Ps_matrix^(-1) ;
matprec := minprec(mat);

Qpht := pAdicField(p, Min([matprec, NE1E2Ps, Nhts]));
heights_vector := Matrix(Qpht, g+1,1, [ht : ht in heights]);
height_coeffs := ChangeRing(mat, Qpht)*heights_vector;

c := height_coeffs[3,1];
//printf "local heights at %o are multiples of %o*log(7)\n", 7, lindepQp(c/Log(pAdicField(p,N-2)!7));

away_contributions := [a*c : a in all_factors_away];
"away_contributions", away_contributions ;
// so the global height is of the form sum_i height_coeffs[i]*Psi[i], where 
// Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)
//
Nhtcoeffs := minprec(height_coeffs); // Precision of height_coeffs
c3 := minval(height_coeffs);
min_root_prec := N;  // smallest precision of roots of QC function

F_list := [**];
for l := 1 to numberofpoints do
  if G_list[l] eq 0 then
    F_list[l] := 0;
  else
    // now find the locally analytic function that extends the global height.
    global_height := &+[height_coeffs[j,1]*Eltseq(E1_E2_list[l])[j] : j in [1..g]];
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
 
c2 := Min([0, valbetafil, minvaleqsplit, valbetafil+ minvaleqsplit]); 
     
i0 := 0;
i0_threshold := Min([valeta, valbetafil/2, (minvalgammafil-c2)/2]);
repeat 
  i0 +:= 1;
until -Floor(log(p,i0)) le i0_threshold;

function valF(i) 
  // lower bound on valuations of coefficients in entries of F_list
  assert i ge i0;
  valgammafili := i le maxdeggammafil select minvalgammafil else 0;
  return -2*Floor(log(p,i)) +c1 + Min(c2,c3+2*minvalchangebasis);
end function;


/*
// Write the height pairing as a linear combination of the basis of symmetric bilinear
// pairings dual to the E1_E2-basis of the auxiliary points. Also solve for h2-constant c
E1_E2_Ps_matrix := Matrix(E1_E2_P_vectors);
local_heights_vector := Matrix(g+1,1,[ht : ht in local_heights]);
height_coeffs := Eltseq(E1_E2_Ps_matrix^(-1)*local_heights_vector);

c := height_coeffs[3];
//printf "local heights at %o are multiples of %o*log(7)\n", 7, lindepQp(c/Log(pAdicField(p,N-2)!7));

away_contributions := [a*c : a in all_factors_away];
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
 */

zero_list := [* *];
sol_list  := [* *];
Nend := Integers()!Min(Ncurrent, Nhtcoeffs); // Precision used for root finding 


// ==========================================================
// ===                    FIND ZEROES                     ===
// ==========================================================

for i := 1 to numberofpoints do
  sol_list[i] := []; 
  zero_list[i] := []; 
  if F_list[i] ne 0 then
    Pp := Qppoints[i];
    xt, bt := local_coord(Pp,prec,data);
    W0invxt := Evaluate(W0^(-1), xt);
    b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
    yt := &+[W0invxt[2,j]*b_vector[j,1] : j in [1..Degree(Q)]];
    if not &and[Valuation(Coefficient(F_list[i],j)) - valF(j) 
                      ge 0 : j in [i0..Degree(F_list[i])]] then
      error "Valuations of coefficients violate lower bound,
          so the quadratic Chabauty function cannot be correct. 
            This is a bug -- please report!"; 
    end if;

    for contrib in away_contributions do
      // solve F_list[i] = contrib 
      f := Evaluate(Qptt!(F_list[i]-contrib),p*Qptt.1);
      precf := Precision(f)[1];
      // Compute roots of f(t) = F(pt)
      bound_val_coeffs_f := valF(precf) + precf;
      if bound_val_coeffs_f lt N then  // Lemma 4.7
        error "TODO: Lower p-adic precision if t-adic prec is too small";
      end if;
      roots, root_prec, f := roots_with_prec(f, Nend);

      if not IsEmpty(roots) then
        roots_precs := [root_prec];
        if #roots gt 1 then 
          // Recenter and rescale so that there is precisely one root
          // in the unit ball
          sep_ints := separate([rt[1] : rt in roots]);
          // sep_int[i] is the smallest n such that roots[i] is distinct
          // from the other roots modulo p^n
          for j := 1 to #roots do
            r := roots[j,1];
            // move r to 0
            f_shifted :=Evaluate(f, Qptt.1+r);
            // new_f = f(p^(s+1)*(t+r)), s  = sep_ints[j]
            new_f:= Evaluate(f_shifted, p^(1+sep_ints[j])*Qptt.1);
            precnewf := Precision(new_f)[1];
            bound_val_coeffs_new_f := precnewf*(sep_ints[j]+1) + valF(precnewf);        
            
            if bound_val_coeffs_new_f lt N then  // Lemma 4.7
              error "TODO: Lower p-adic precision if t-adic prec is too small";
            end if;
            // Compute roots of f(p^(s+1)*(t+r))
            new_roots, new_root_prec := roots_with_prec(new_f, Nend);
            // check that there is only one root. otherwise there's a bug.
            assert #new_roots eq 1; 
            // if the shifted and scaled root isn't quite zero, decrease precision
            // accordingly.
            new_root_prec := Min(new_root_prec, Valuation(new_roots[1,1]));
            roots_precs[j] := Max(new_root_prec+sep_ints[j]+1, root_prec);
            min_root_prec := Min(min_root_prec, roots_precs[j]);
            // minimal precision to which a root of F is known.
          end for;
        else 
          min_root_prec := Min(min_root_prec, root_prec);
        end if; // #roots gt 1

        known := false;
        for j := 1 to #roots do
          r := roots[j,1];
          ChangePrecision(~roots[j,1], roots_precs[j]);  // Lemma 4.7
          // p*r is correct to roots_precs[j]+1 digits
          Qproot := pAdicField(p, roots_precs[j] + 1); 
          // So pt is provably correct to the precision of Qproot
          pt := [Qproot!Evaluate(c, p*r) : c in [xt, yt]];
          for k := 1 to #sol_list do 
            // Check if this solution is already known
            if #sol_list[k] gt 0 then 
              for l := 1 to #sol_list[k] do
                sol := sol_list[k,l,1];
                if are_congruent(pt, sol) then
                  // pt already known -> multiple root
                  sol_list[k,l,2] := true;
                  known := true;
                end if;
              end for;
            end if;
          end for; // k := 1 to #sol_list do 
          if not known then
            if roots[j][2] le 0 then  // TODO: want <= root_prec??
              Append(~sol_list[i], <pt, true>); // multiple root
            else 
              Append(~sol_list[i], <pt, false>); // simple root
            end if;
          end if;
        end for; // j:=1 to #roots
      end if; // not IsEmpty(roots)
      zero_list[i] := roots;

    end for; // contrib in away_contributions
  end if; // F_list[i] ne 0
end for;  // i:=1 to numberofpoints

if pl gt 0 then
  printf " All roots of the quadratic Chabauty function(s) are correct to precision at least %o^%o.\n", p, min_root_prec;
end if;

// ==========================================================
// ===                    SANITY CHECK                    ===
// ==========================================================

/*
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
    if pl gt 2 then  print good_affine_rat_pts_xy[j], "Valuation of the quadratic Chabauty function minus sum of contributions away from p", vals; end if;
    assert exists(v){ val : val in vals | val ge Nend/2};
  count := count+1;
  end if;
end for;
"Sanity check passed";
*/


K := pAdicField(p, min_root_prec);
fake_rat_pts := [* *]; 
recovered_rat_pts_count := 0;
number_of_known_rat_pts := #good_affine_rat_pts_xy;
sols := &cat[L : L in sol_list | #L gt 0];
for i := 1 to #sols do
//    P := [lindepQp(sols[i,1]), lindepQp(sols[i,2])];
  known_rational := false;
  sol := sols[i,1];
  multiple := sols[i,2];
  for pt in good_affine_rat_pts_xy do
    // Check if sols is congruent to a known rational point
    if are_congruent(sols[i,1], pt) then
    //if IsZero(K!sols[i,1] - K!pt[1]) and IsZero (K!sols[i,2] - K!pt[2]) then
      if pl gt 1 then " Recovered known rational point", pt; end if;
      if multiple then 
        error "Multiple root at rational point. Try increasing p-adic precision (parameter N).";
      end if;
      known_rational := true;
      recovered_rat_pts_count +:= 1;
      break;
    end if;
  end for;
  if not known_rational then
    P := [lindepQp(K!sols[i,1,1]), lindepQp(K!sols[i,1,2])];
    //if pl gt 0 then printf "Rational reconstruction of point %o is \%o ", i,P; end if;
    if IsZero(eval_Q(Q, P[1], P[2])) then
      if pl gt 1 then " Found unknown rational point P", P; end if;
      if multiple then 
        error "Multiple root at rational point. Try increasing p-adic precision (parameter N).";
      end if;
      Append(~good_affine_rat_pts_xy, P); 
    else 
      Append(~fake_rat_pts, sols[i,1]); 
      if pl gt 1 then 
        printf " Solution %o does not seem to be rational.\n", sols[i,1]; 
      end if;
      // Here multiple roots are fine.
    end if;
  end if;
end for;
if number_of_known_rat_pts gt recovered_rat_pts_count then
  error "Not all known rational points in good disks where recovered.";
end if;


fake_rat_pts_inf := fake_rat_pts;
good_rat_pts_inf := good_affine_rat_pts_xy;


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
fake_rat_pts_inf := [[P[1],P[2]] : P in fake2 | Valuation(P[1]) gt 0];

Xpts := [X!P : P in good_rat_pts_affine];
good_pts3 := [pi(X_inf!P) : P in good_affine_rat_pts_xy cat bad_affine_rat_pts_xy];
for P in good_pts3 do
  Include(~Xpts, P);
end for; 
small_pts := Points(X : Bound := 1000); // check we're not missing any small points
assert &and[P in Xpts : P in small_pts];

"";
"Run the Mordell-Weil sieve to show there are no additional rational points in affine disks.";


printf "\nStill need to look at infinite disks\n";
base_pt_inf := Eltseq(phi(X!base_pt));
J_inf := Jacobian(X_inf);
bas_inf := [Evaluate(phi, P) : P in bas];
divisors_inf := [* [* [[-1,-1]],[[1,7]]*],    [* [[2,-35]], [[4,209]] *]*];
P1_inf := Evaluate(phi, P1);
P2_inf := Evaluate(phi, P2);
splitting_generators := [P1_inf,P2_inf];
"Use independent points", splitting_generators;
splitting_indices := [[0,-1], [-5,-4]];
fake_coeffs_mod_pN_inf, rat_coeffs_mod_pN_inf := coefficients_mod_pN(fake_rat_pts_inf, good_rat_pts_inf, divisors_inf, base_pt_inf, splitting_indices, data_hol_inf); 
fake_coeffs_inf := [* *];
Append(~fake_coeffs_inf, [ fake_coeffs_mod_pN_inf ]);

qc_M := p^3;
M := qc_M;
qc_fake_coeffs_mod_M_inf := coeffs_CRT(fake_coeffs_inf, [p], [3]);
"number of cosets", #qc_fake_coeffs_mod_M_inf;
"Start the Mordell-Weil sieve to show there are no additional rational points in disks at infinity.";
  time done_fake_inf, bool_list_inf, satknown_inf, satunknown_inf := MWSieve(J_inf, mws_primes, M, bas_inf cat [], X_inf!base_pt_inf, qc_fake_coeffs_mod_M_inf : known_rat_coeffs := rat_coeffs_mod_pN_inf );

"done with the Mordell-Weil sieve?", done_fake;
"For sieving used the prime(s)", mws_primes;




Q:=y^2 -( x^6+2*x^4+6*x^3+17*x^2+18*x+5 );
