// July 21: JSM/JB added precision estimates
// August 21: ND added use_polys

load "coleman.m";
load "symplectic_basis.m";
load "hecke_correspondence.m";
load "hodge.m";
load "frobenius.m"; 
load "heights.m";
load "second_patch_quartic.m";


function QCModAffine(Q, p : N := 15, prec := 2*N, basis0 := [], basis1 := [], basis2 := [], 
    number_of_correspondences := 0, printlevel := 0, debug := false, base_point := 0, 
    hecke_prime := 0, unit_root_splitting := false, eqsplit := 0,
  height_coeffs := [], rho := 0, use_log_basis := false, use_polys:=[]);
//nice_correspondences := [], away_contributions := [0], 

// INPUT
//  * Q is a bivariate polynomial with integer coefficients, defining a smooth affine plane curve
//    such that its smooth projective model X and J = Jac(X) satisfy
//    * rk(J/Q) = g(X) 
//    * J has RM over Q
//    These conditions are not checked!
//  * p is a prime of good reduction, satisfying some additional Tuitman conditions (these
//    are checked).
//
//  OPIONAL PARAMETERS
//  * N is the p-adic precision used in the computations
//  * prec is the t-adic precision used for power series computations
//  * basis0 is a basis of the holomorphic differentials
//  * basis1 is a set of g independent meromorphic differentials s.t. basis0 and basis0
//     generate H^1_dR(X).
//  * Together with basis0, basis1, the sequence basis2 forms a basis of H^1_dR(U), where 
//    U is the affine patch we work on (bad disks removed).
//  * number_of_correspondences is the number of quadratic Chabauty functions used for
//    finding the rational points. 
//  * printlevel determines how much information is printed during the computation. 
//  * debug is a boolean determining whether some additional checks should be performed.
//  * if debug is true, some additional checks and included and additional information is
//    printed 
//  * base_point is a pair [x,y] specifying a rational point on X to be used as a base
//    point for Abel Jacobi. If base_point = 0, the first good affine rational point found
//    is used.
//  * hecke_prime is a prime number q such that the Hecke operator Tq is used to construct
//    nice correspondences and (if use_log_basis is false) a basis of the bilinear pairings.
//    If hecke_prime is 0, we use q=p. We check p-adically whether Tq generates the
//    Hecke algebra, which is needed below, but for provably correct output, this should be
//    checked by an exact computation, as in QCModQuartic.
//  * if use_log_basis is false, we determine a basis of bilinear pairings as the dual
//    basis of the E1\otimes E2-basis for sufficiently many rational points on X. Otherwise we
//    use a basis given by products of logs (i.e. single integrals of holomorphic forms). 
//    The latter is necessary if there are not enough rational points on X.
//  * height_coeffs specifies the coefficient of the height pairing in terms of a basis of
//    bilinear pairings as in use_log_basis.
//  * eqsplit is a 2g x g matrix representing an equivariant splitting of the Hodge
//    filtration wrt the given basis.
//  * unit_root_splitting is true if we need to use the unit root splitting, else false.
//
//  OUTPUT:
//  ** good_affine_rat_pts_xy, bool, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints **
//  where
//  * good_affine_rat_pts_xy is a list of rational points (x,y) such that Q(x,y)=0 living
//    in good residue disks (terminology as in Balakrishnan-Tuitman, Explicit Coleman integration for curves 
//  * bool is true iff the computation proves that good_affine_rat_pts_xy is the complete
//    list of affine rational points in good residue disks
//  * bad_affine_rat_pts_xy is a list of bad rational points (x,y) such that Q(x,y)=0. 
//  * data is the Coleman data at p used in the algorithm.
//  * fake_rat_pts is a list of solutions to the quadratic Chabauty equations which appear
//    to be non-rational. This should be empty iff bool is true.
//  * bad_Qppoints is a list of Qppoints representing bad residue disks.
//  
//  EXAMPLE
//  f67  := x^6 + 2*x^5 +   x^4 - 2*x^3 + 2*x^2 - 4*x + 1; 
//  good_pts, bool, bad_pts, data, fake_rat_pts, bad_disks := QCModAffine(y^2-f67, 7);
//


  // ==========================================================
  // ===                   CHECK INPUT                      ===
  // ==========================================================
  



  // ==========================================================
  // ===                  INITIALIZATION                    ===
  // ==========================================================

  // Increase precision if it's too small compared to p-adic precision
  while  prec - 2*Log(p, prec) le N-5 do  // 5 comes from the constant c in the lower bound TODO: add ref.
    prec +:= 1; 
  end while;
    
  QQ := Rationals();
  Qp := pAdicField(p,N);
  r,Delta,s := auxpolys(Q);

  pl := printlevel;
  if debug then pl := 3; end if;

  // ==========================================================
  // ===               SYMPLECTIC BASIS                  ===
  // ==========================================================

  if pl gt 1 then print " Computing a symplectic basis of H^1"; end if;
  h1basis, g, r, W0 := h1_basis(Q,p,N);  
  if #basis0*#basis1 gt 0 then // Use the given basis
    h1basis := basis0 cat basis1;
  end if;
  if pl gt 2 then printf " genus = %o.\n", g; end if;
  if IsZero(rho) then 
    rho := g;       //If not given, we assume that the Picard number is equal to the genus
  end if;
  
  if number_of_correspondences eq 0 then
    number_of_correspondences := rho-1; 
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
      cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec := cpm_prec);
      // If this takes very long, try 
      // cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec := cpm_prec, split := false);
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
  if pl gt 1 then printf " Computed Coleman data at p=%o to precision %o.\n", p,N; end if;

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
  if pl gt 1 then printf "\n Using the base point %o.\n", bQ_xy; end if;
  good_affine_rat_pts_xy_no_bpt := Remove(good_affine_rat_pts_xy, global_base_point_index); 

  ks := Exclude(good_Q_Qp_indices, local_base_point_index);  // indices in Qppoints of good affine 
                                                             // rational points with base point removed
  

  // compute Teichmueller representatives of good points
  teichpoints := [**]; 
  for i := 1 to numberofpoints do
    teichpoints[i] := is_bad(Qppoints[i],data) select 0  else teichmueller_pt(Qppoints[i],data); // No precision loss
  end for;

  // ==========================================================
  // ===                  CORRESPONDENCES                 ===
  // ==========================================================

  if pl gt 1 then printf "\n Computing correspondences";  end if;

  // Want rho-1 independent `nice` correspondences.
  // Construct them using powers of Hecke operator
  q := IsZero(hecke_prime) select p else hecke_prime;
  correspondences, Tq, corr_loss := hecke_corr(data,q,N : basis0:=basis0,basis1:=basis1,printlevel:=pl,use_polys:=use_polys);

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
  if q ne p then
    printf "\n WARNING: Using Hecke operator T_%o, but %o isn't our working prime %o. The result will not be provably correct.\n", q, q, p; 
  end if;  

  if #use_polys eq 0 then
    // Check if Hecke operator generates. Need to do this using p-adic arithmetic.
    if Dimension(sub<mat_space | ChangeUniverse(correspondences, mat_space)>) lt rho-1 then
      error "Powers of Hecke operator don't suffice to generate the space of nice correspondences";
    end if;
  end if;

  //end if;
    
  if pl gt 1 then printf "\n Nice correspondences:\n%o\n\n", correspondences; end if;

  Tq_small := ExtractBlock(Tq,1,1,g,g);                // Hecke operator at q on H^0(X,Omega^1)
  char_poly_Tq := CharacteristicPolynomial(Tq_small);  
  Qp_ext := quo<PolynomialRing(Qp) | char_poly_Tq>;
  Salpha := quo<PolynomialRing(S) | char_poly_Tq>;

  // Compute an End0(J)-equivariant splitting of the Hodge filtration.
  
  if IsZero(eqsplit) then
    if unit_root_splitting then 
      // Compute the unit root splitting 
      FQp := ChangeRing(Submatrix(data`F,1,1,2*g,2*g), Qp); // Frobenius over Qp
      char_poly_frob := CharacteristicPolynomial(FQp);
      fact := Factorisation(char_poly_frob);
      assert #fact ge 2;
      non_unit_root_char_poly := &*[t[1]^t[2] : t in fact | &and[Valuation(Coefficient(t[1],i)) gt 0 : i in [0..Degree(t[1])-1]]];
      assert Degree(non_unit_root_char_poly) eq g;
      Mp := EchelonForm(ChangeRing(Evaluate(non_unit_root_char_poly, FQp), pAdicField(p, N-2))); 
      assert Rank(Mp) eq g;
      // basis of the unit root subspace wrt symplectic basis
      W_wrt_simpl := Transpose(Submatrix(ChangeRing(Mp, Rationals()), 1,1,g,2*g));
      // the splitting matrix is the unique matrix leaving the holomorphic
      // differentials invariant and vanishing along the unit root subspace.
      W_lower := ExtractBlock(W_wrt_simpl, g+1, 1, g, g);
      W_upper_minus := [-Vector(RowSequence(W_wrt_simpl)[i]) : i in [1..g]];
      split := Transpose(Matrix(Solution(W_lower, W_upper_minus)));
      eqsplit := BlockMatrix(2, 1, [IdentityMatrix(Rationals(),g), split]);
    else 
      eqsplit := eq_split(Tq);
    end if; // unit_root_splitting
  end if; // IsZero(eqsplit)

  // Test equivariance of splitting 
  big_split := BlockMatrix(1,2,[eqsplit,ZeroMatrix(Rationals(),2*g,g)]);
  check_equiv := ChangeRing((big_split*Transpose(Tq) - Transpose(Tq)*big_split), pAdicField(p, N-2));     
  min_val_check_equiv := Min([Min([Valuation(check_equiv[i,j]) : j in [1..g]]): i in [1..2*g]]);
  assert min_val_check_equiv ge N-3; 
  //assert IsZero(big_split*Transpose(Tq) - Transpose(Tq)*big_split);     // Test equivariance
  if pl gt 1 then printf "\n equivariant splitting:\n%o\n", eqsplit; end if;
  minvaleqsplit := minvalp(eqsplit, p);


  F_lists := [* *]; // functions vanishing in rational points, one for each corresp
  zeroes_lists := [* *]; // zeroes of functions in F_lists; these are centered at 0, i.e. shifted 
  sols_lists := [* *]; // p-adic points corresponding to zeroes. 
  local_height_lists := [* *]; // local height as power series 
  E1_E2_lists := [* *]; // E1 tensor E2 as power series
  E1_lists := [* *]; 
  E2_lists := [* *]; 
  NE1E2Ps := Ncorr;  // Precision of E1 tensor E2 of auxiliary points
  Nhts := Ncorr; // Precision of local heights of auxiliary points
  Nexpansions := []; // Precision of power series expansion of local heights 
  c1s := [];
  valetas := [];
  valbetafils := [];
  maxdeggammafils := [];
  minvalgammafils := []; 
  if #height_coeffs eq 0 or not use_log_basis then 
    heights := [* *];    // heights of auxiliary points. Different correspondences allowed (might cut down the # of necessary rational pts).
    E1P := 0;
    super_space := VectorSpace(Qp, g);
    E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
    E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
  end if;
  

  for l := 1 to number_of_correspondences do
    Z := correspondences[l];

    // ==========================================================
    // ===                     HODGE                       ===
    // ==========================================================
    
    if pl gt 0 then printf  " Computing Hodge filtration for correspondence %o.\n", l; end if;

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

    if pl gt 0 then 
      printf  " eta =  %o.\n", eta; 
      printf  " beta_fil  =  %o.\n", betafil; 
      printf  " gamma_fil =  %o.\n\n", gammafil; 
    end if;

    Append(~valetas, minvalp(eta, p));
    Append(~valbetafils, minvalp(betafil, p));
    Append(~maxdeggammafils, Max([Degree(a) : a in Eltseq(gammafil)]));
    Append(~minvalgammafils, 
        Min([Min([0] cat [Valuation(c, p) : c in Coefficients(a)]) : a in Eltseq(gammafil)]));

    // ==========================================================
    // ===                  FROBENIUS                      ===
    // ==========================================================
     
    b0 := teichmueller_pt(bQ,data); 
    if pl gt 0 then printf  " Computing Frobenius structure for correspondence %o.\n", l; end if;
    b0pt := [QQ!c : c in xy_coordinates(b0, data)]; // xy-coordinates of P
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
    Append(~c1s, Min(minvalPhiAZbs)); 

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


    minvalchangebasis := 0;
    if #height_coeffs eq 0 or not use_log_basis then // Compute heights of auxiliary points.

      if IsZero(E1P) then  // Find a point with non-zero E1 to write down a basis of the Lie algebra. 
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
      end if; // IsZero(E1P)


      changebasis:=Matrix(basisH0star)^(-1);
      minvalchangebasis := minval(changebasis);
      if pl gt 1 then 
        printf " Using point %o at correspondence %o to generate.\n", 
                                  good_affine_rat_pts_xy_no_bpt[min_i],l; 
      end if;

    end if; //#height_coeffs eq 0 or not use_log_basis then 

    // heights contains the list of heights of auxiliary points
    if #height_coeffs eq 0 then // Compute heights of auxiliary points.
      if #heights lt g then  // add E1_E2(P) to known subspace until dimension is g.
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
          NE1E2P := Min(Ni,minprec(E1_E2_P));
          NLA := Integers()!Min(Precision(BaseRing(E1_E2_subspace)), NE1E2P);
          // p^NLA is the precision for the linear algebra computation.
          new_super_space := VectorSpace(pAdicField(p, NLA), g);
          old_basis := ChangeUniverse(Basis(E1_E2_subspace), new_super_space); 
          new_E1_E2_subspace := sub<new_super_space | old_basis cat [new_super_space!Eltseq(E1_E2_P)]>;
          if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
            E1_E2_subspace := new_E1_E2_subspace; 
            if pl gt 1 then printf " Using point %o at correspondence %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i],l; end if;

            gammafilP := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qpti,data);
            height_P := height(Phii,betafil,gammafilP,eqsplit,data);
            NhtP := AbsolutePrecision(height_P); 
            Append(~heights, height_P); // height of A_Z(b, P)
            Append(~E1_E2_Ps, E1_E2_P);
            Nhts := Min(Nhts, NhtP);
            NE1E2Ps := Min(NE1E2Ps, NE1E2P);
          end if;
          i +:= 1;
        until #heights eq g or i gt #ks; 
      end if; // #heights lt g 
    end if; // #height_coeffs eq 0
    local_height_list := [*0 : k in [1..numberofpoints]*];
    E1_E2_list := [*0 : k in [1..numberofpoints]*];
    E1_list := [*0 : k in [1..numberofpoints]*];
    E2_list := [*0 : k in [1..numberofpoints]*];
    for k := 1 to numberofpoints do
      if G_list[k] ne 0 then

        local_height_list[k] := height(PhiAZb_to_z[k],betafil,gammafil_listb_to_z[k],eqsplit,data);
        if use_log_basis then 
          E1_list[k] := [PhiAZb_to_z[k,j,1] : j in [2..g+1]];
          E2_list[k] := [PhiAZb_to_z[k,2*g+2,g+1+j] - betafil[j] : j in [1..g]]; 
        else 
          E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,changebasis,data,Salpha);
        end if;
      end if;
    end for;  // k := 1 to numberofpoints 
     
    Append(~local_height_lists, local_height_list);
    Append(~E1_E2_lists, E1_E2_list);
    Append(~E1_lists, E1_list);
    Append(~E2_lists, E2_list);
    Append(~Nexpansions, Ncurrent);

  end for; // l := 1 to number_of_correspondences 

  if #height_coeffs eq 0 and #heights lt g then
    error "Not enough rational points on the curve!"; // to span the symmetric square of the Mordell-Weil group";
  end if;

  if #height_coeffs eq 0 then 
    // Write the height pairing as a linear combination of the basis of symmetric bilinear
    // pairings dual to the E1_E2-basis of the auxiliary points. 
    E1_E2_Ps_matrix := Matrix(pAdicField(p, NE1E2Ps), [Eltseq(E1_E2) : E1_E2 in E1_E2_Ps]);
    mat := E1_E2_Ps_matrix^(-1) ;
    matprec := minprec(mat);
    Qpht := pAdicField(p, Min([matprec, NE1E2Ps, Nhts]));
    heights_vector := Matrix(Qpht, g,1, [ht : ht in heights]);
    height_coeffs := ChangeRing(mat, Qpht)*heights_vector;
    // so the global height is of the form sum_i height_coeff[i]*Psi[i], where 
    // Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)
  end if;
  Nhtcoeffs := minprec(height_coeffs); // Precision of height_coeffs
  c3 := minval(height_coeffs);
  min_root_prec := N;  // smallest precision of roots of QC function


  // Find expansion of the quadratic Chabauty function

  for k := 1 to number_of_correspondences do

    F_list := [**];
    for l := 1 to numberofpoints do
      if G_list[l] eq 0 then
        F_list[l] := 0;
      else
        if use_log_basis then
          global_height := 0;
          E1 := E1_lists[k,l]; E2 := E2_lists[k,l];
          for i := 1 to g do
            for j := i to g do
              global_height +:= -1/2*height_coeffs[i,j]*(E1[i]*E2[j] + E1[j]*E2[i]);
            end for;        
          end for;        

        else
          global_height := &+[height_coeffs[j,1]*Eltseq(E1_E2_lists[k,l])[j] : j in [1..g]];
        end if;
        F_list[l] := global_height - local_height_lists[k,l];
      end if;

    end for; // l := 1 to numberofpoints 
    if pl gt 2 then
      printf " Power series expansions of the quadratic Chabauty functions at correspondence %o in all good affine disks, capped at precision %o\n", k, 3;  
      for i := 1 to #F_list do
        if F_list[i] ne 0 then 
        printf " disk %o\n expansion: %o \n\n", [Fp!(Qppoints[i]`x), Fp!(Qppoints[i]`b[2])], ChangePrecision(F_list[i], 3);
        end if;
      end for;
    end if; 
     
    Append(~F_lists, F_list);

    c2 := Min([0, valbetafils[k], minvaleqsplit, valbetafils[k]+ minvaleqsplit]); 
     
    i0 := 0;
    i0_threshold := Min([valetas[k], valbetafils[k]/2, (minvalgammafils[k]-c2)/2]);
    repeat 
      i0 +:= 1;
    until -Floor(log(p,i0)) le i0_threshold;

    function valF(i) 
      // lower bound on valuations of coefficients in entries of F_list
      assert i ge i0;
      valgammafili := i le maxdeggammafils[k] select minvalgammafils[k] else 0;
      return -2*Floor(log(p,i)) +c1s[k] + Min(c2,c3+2*minvalchangebasis);
    end function;

    zero_list := [* *];
    sol_list  := [* *];
   
    Nend := Integers()!Min(Nexpansions[k], Nhtcoeffs); // Precision used for root finding 

    if pl gt 0 then
      printf " The quadratic Chabauty function for correspondence %o is correct to precision %o^%o.\n",  k, p, Nend;
    end if;
    Qp_small   := pAdicField(p,Nend); 
    Qptt := PowerSeriesRing(Qp_small,prec);
    Zp_small   := pAdicRing(p,Nend);
    Zpt  := PolynomialRing(Zp_small);
    Qpt  := PolynomialRing(Qp_small);
    //
    // ==========================================================
    // ===                 FIND ZEROES                     ===
    // ==========================================================

    for i := 1 to numberofpoints do
      sol_list[i] := []; 
      zero_list[i] := []; 
      if G_list[i] ne 0 then
        Pp := Qppoints[i];
        // find affine local coordinates 
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
        //for contrib in away_contributions do
        // solve F_list[i] = 0
        //f := Evaluate(Qptt!(F_list[i]-contrib),p*Qptt.1);
        //
        f := Evaluate(Qptt!(F_list[i]),p*Qptt.1);
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
        //end if; // number_of_roots gt 0
      end if; // G_list[i] ne 0
    end for;  // i:=1 to numberofpoints 

    Append(~zeroes_lists, zero_list);
    Append(~sols_lists, sol_list);
  end for;  // k := 1 to number_of_correspondences do
  if pl gt 0 then
    printf " All roots of the quadratic Chabauty function(s) are correct to precision at least %o^%o.\n", p, min_root_prec;
  end if;


  
  // ==========================================================
  // ===                 SANITY CHECK                       ===
  // ==========================================================

  /*
   * Commented out, since we now check that all known rational points are recovered below.
   * This check was not entirely stable due to a missing precision analysis for the
   * evaluation of the QC function.
   *
  for i := 1 to number_of_correspondences do
    if pl gt 0 then printf "\n Sanity check at rational points for correspondence %o.  ", i; end if;
    // TODO: bound precision loss in evaluation
    F_list := F_lists[i]; 
    for j in [1..#good_Qpoints] do
      P := good_Qpoints[j]; 
      ind := FindQpointQp(P,Qppoints); 
      Pp := Qppoints[ind];
      //vals := [];
      if ind gt 0 and (is_bad(Qppoints[ind],data) eq false) and (P`inf eq false) then		
//      for contrib in away_contributions do
//        Append(~vals,  Valuation(Qp_small!Evaluate(F_list[ind]-contrib,P`x - Pp`x))); 
//      end for;
        val := Valuation(Qp_small!Evaluate(F_list[ind], P`x - Pp`x)); 
        // F_list[ind] = contrib for some away contribution contrib
        if pl gt 1 then  printf "\nValuation of the quadratic Chabauty function evaluated at (x,y) = %o is \n%o\n", good_affine_rat_pts_xy[j], p,  val; end if;

        assert val ge Nend-1;  // possible precision loss in evaluating F
        //assert exists(v){ val : val in vals | val ge Nend-1}; // possible precision loss in evaluating F

      end if;
    end for;
  end for; //  i := 1 to number_of_correspondences 
  if pl gt 0 then  printf "\nSanity checks passed.\n"; end if;
  */
  

  // ==========================================================
  // ===               COMMON SOLUTIONS                     ===
  // ==========================================================

  if pl gt 2 then for l := 1 to number_of_correspondences do 
      printf "\n The list of solutions constructed from correspondence %o is \n %o \n\n", l, sols_lists[l]; 
    end for; end if;
  solutions := sols_lists[1];
  for i in [1..#Qppoints] do // residue disks
    if not IsEmpty(solutions[i]) then
      len := #solutions[i];
      include := [1..len];
      for j := 1 to len do // solutions for first correspondence
        //"i,j", i,j; solutions[i];
        pt1 := solutions[i,j,1];  
        for l := 2 to number_of_correspondences do // correspondences
          matched := false;
          for k := 1 to #sols_lists[l][i] do // solutions for lth correspondence
            pt2 := sols_lists[l,i,k,1];
            if are_congruent(pt1, pt2) then
              matched := true;
              solutions[i,j,2] and:= sols_lists[l,i,k,2]; 
              // A point is a multiple solution if it's a multiple solution for all correspondences.
            end if;
          end for;
          if not matched then
            Exclude(~include, j);
          end if;
        end for;
      end for;
      //"include", include;
      solutions[i] := [solutions[i,j] : j in include];
    end if; // not IsEmpty(solutions[i]) then
  end for; // i in [1..#Qppoints] 


  // solutions[i] contains the common solutions in the ith residue disk
  sols := &cat[L : L in solutions | #L gt 0];
  if pl gt 0 then printf "\n The common roots of the quadratic Chabauty function(s) in this affine patch are \n %o \n\n", [t[1] : t in sols]; end if; 
  if pl gt 1 then printf " The lists of zeroes are \n %o \n", zeroes_lists; end if; 
  K := pAdicField(p, min_root_prec);
  fake_rat_pts := [* *]; 
  recovered_rat_pts_count := 0;
  number_of_known_rat_pts := #good_affine_rat_pts_xy;
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

  if #fake_rat_pts gt 0 then
    return good_affine_rat_pts_xy, false, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints;
  else
    return good_affine_rat_pts_xy, true, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints;
  end if;

end function;



function hecke_operator_generates(S, p)
  // S is a space of cusp forms
  // Check that the Hecke operator Tp generates the Hecke algebra
  Tp := HeckeOperator(S, p);
  return not IsDiagonal(Tp) and Degree(MinimalPolynomial(Tp)) eq Dimension(S) div 2;
end function;



function QCModQuartic(Q, S : p := 3, bound := 100, number_of_correspondences := 2, 
                printlevel := 0, known_pts := [], height_bd := 10^4, debug := false, base_point := 0,
                N := 15, prec := 2*N, max_inf_deg := 6 )


  // S is a space of cusp forms
  // Q is a polynomial in (QQ[x])[y] of total degree 4
  if LeadingCoefficient(Q) ne 1 then 
    error "Need a monic model in y"; 
    // TODO: 
    // - Automatically compute a Tuitman model that contains enough rational points 
  end if;
  C, Qxy := curve(Q);
  assert Degree(Qxy) eq 4;
  P2 := Ambient(C);
  X := P2.1; Y := P2.2; Z := P2.3;
  pl := printlevel;
  
  p -:= 1;
  while p lt bound do
    p := NextPrime(p);
    bool := false;
    if (not IsDivisibleBy(Level(S), p)) and hecke_operator_generates(S, p) then
      // Find a good second affine patch so that
      // - every residue disk is good (i.e. is affine and the Frobenius lift is defined
      //   there) on at least one affine patch
      // - every affine patch contains enough rational points to fit the height pairing.

      if pl gt 1 then 
        printf "\n Find a good second affine patch\n"; // so that the lift of Frobenius is defined for every point on at least one affine patch.";
      end if;
      try
        Q_inf, A := second_affine_patch(Q, p : printlevel := printlevel, bd := 4, max_inf_deg := max_inf_deg);
      catch e
        if pl gt 0 then 
        printf "\n Error at p = %o: %o\n", p, e; end if;
        continue;
      end try;

      if pl gt 0 then 
        printf "\n Starting quadratic Chabauty computation for the affine patch \n %o = 0\n at the prime p = %o\n\n", Q, p;
      end if;
      try 
        good_pts1, bool1, bad_pts1, data1, fake_pts1, bad_disks1 := QCModAffine(Q, p : number_of_correspondences := number_of_correspondences, printlevel := printlevel, debug := debug, base_point := base_point, N:=N, prec:=prec);
        if not bool1 then  "non-rational common roots (remove this message)"; continue; end if;
      catch e
        if pl gt 1 then printf "\n Error in qc computation at p = %o:\n %o \n",p, e; end if;
        continue;
      end try;
      try
        if pl gt 0 then 
          printf "\n Starting quadratic Chabauty computation for the affine patch \n %o = 0\n at the prime p = %o\n\n", Q_inf, p;
        end if;
        good_pts2, bool2, bad_pts2, data2, fake_pts2, bad_disks2 := QCModAffine(Q_inf, p : number_of_correspondences := number_of_correspondences, printlevel := printlevel, debug := debug, N:=N, prec:=prec);
        if not bool2 then "non-rational common roots"; continue; end if;
      catch e
        if pl gt 0 then printf "\n Error in qc computation at p = %o\n", p; end if;
        if pl gt 1 then e; end if;
        continue;
      end try;

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
      small_pts := Points(C : Bound := height_bd); // check we're not missing any small points
      for P in small_pts do Include(~known_pts, P); end for;
      if #known_pts gt #Cpts then
        error "Not all known rational points were recovered.";
      end if;

      return true, Cpts, p, Q_inf;  
    end if; // (not IsDivisibleBy(Level(S), p)) and hecke_operator_generates(S, p) 
  end while;
  return false, _, _, _; 
end function;


