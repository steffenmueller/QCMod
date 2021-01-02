
load "coleman.m";
load "symplectic_basis.m";
load "hecke_correspondence.m";
load "hodge.m";
load "frobenius.m"; 
load "heights.m";
load "second_patch_quartic.m";


function QCModAffine(Q, p : N := 20, prec := 80, basis0 := [], basis1 := [], basis2 := [], 
    number_of_correspondences := 2, printlevel := 0, debug := false, base_point := 0, 
    hecke_prime := 0, nice_correspondences := [], unit_root_splitting := false, eqsplit := 0,
    height_coeffs := [], away_contributions := [0], rho := 0, use_log_basis := false);

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
//  * nice_correspondences is a list of 2g x 2g matrices specifying correspondences that are 
//    nice in the sense of BBMTV19 via their action on H^1_dR. If nice_correspondences 
//    is 0, they are constructed from powers of Tq.
//  * if use_log_basis is false, we determine a basis of bilinear pairings as the dual
//    basis of the E1\otimes E2-basis for sufficiently many rational points on X. Otherwise we
//    use a basis given by products of logs (i.e. single integrals of holomorphic forms). 
//    The latter is necessary if there are not enough rational points on X.
//  * height_coeffs specifies the coefficient of the height pairing in terms of a basis of
//    bilinear pairings as in use_log_basis.
//  * away_contributions contains the possible values of the quadratic chabauty function,
//    given by sums of local heights away from p.
//  * rho is the Picard number. If rho=0 is given, we assume it's g.  
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
  
  if #away_contributions gt 1 then if #nice_correspondences eq 0 then  
    "Away contributions given, but no correspondence. Assuming that correspondences are constructed from powers of Hecke operator at p";
    // TODO: Maybe this should actually raise an error? Need to specify the correspondence
    //error "Giving nontrivial contributions away from p requires also specifying the 
  //          correspondences used to obtain them.";
 end if; end if;
  if #nice_correspondences gt 0 and number_of_correspondences ne #nice_correspondences then
    error "Number of given correspondences doesn't match number_of_correspondences";
  end if;
  if rho eq 1 then
    error "Quadratic Chabauty requires Picard number > 1";
  end if;
  if use_log_basis and #height_coeffs eq 0 then
    error "To use the basis of bilinear pairings given by products of logs 
    (i.e. single integrals), you have to specify the coefficients of the height pairing.";
  end if;



  // ==========================================================
  // ===                  INITIALIZATION                    ===
  // ==========================================================

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
  if debug then pl := 3; end if;

  // ==========================================================
  // ===               SYMPLECTIC BASIS                  ===
  // ==========================================================

  if pl gt 1 then print "Computing a symplectic basis of H^1"; end if;
  h1basis, g, r, W0 := h1_basis(Q,p,N);  
  if #basis0*#basis1 gt 0 then // Use the given basis
    h1basis := basis0 cat basis1;
  end if;
  if pl gt 1 then printf "genus = %o.\n", g; end if;
  if IsZero(rho) then 
    rho := g;       //If not given, we assume that the Picard number is equal to the genus
  end if;
  
  if number_of_correspondences gt rho-1 then
    number_of_correspondences := rho-1; // No reason to use dependent correspondences
  end if;

  // h1basis is a basis of H^1 such that the first g elements span the regular
  // differentials. Construct a symplectic basis by changing the last g elements of h1basis.
  //
  standard_sympl_mat := ZeroMatrix(Rationals(),2*g,2*g);
  for i in [1..g] do
    standard_sympl_mat[i,g+i] := 1; standard_sympl_mat[g+i,i] := -1;
  end for;

  if pl gt 2 then print "Computing the cup product matrix"; end if;
  cpm_prec := 2*g;
  if assigned cpm then delete cpm; end if;
  repeat 
    try 
      cpm := cup_product_matrix(h1basis, Q, g, r, W0 : prec := cpm_prec);
    catch e;
      cpm_prec +:= g;
    end try;
  until assigned cpm;
  if pl gt 2 then print "Cup product matrix", cpm; end if;
  if cpm ne standard_sympl_mat then 
    coefficients := symplectic_basis(cpm); // Create coefficients of a symplectic basis in terms of h1basis
    new_complementary_basis := [&+[coefficients[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
    sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
    if not &and[&and[Valuation(c, p) ge 0 : c in Coefficients(w[1])] : w in sympl_basis] then
      error "The computed symplectic basis is not integral. Please try a different prime or a different basis.";
    end if; 
    if pl gt 2 then print "Symplectic basis of H^1", sympl_basis; end if;
    basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
    basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
  end if;
  data := coleman_data(Q,p,N : useU:=true,  basis0 := basis0, basis1 := basis1, basis2 := basis2);
  if pl gt 1 then printf "Computed Coleman data at p=%o.\n", p; end if;
  

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
  // TODO: This won't always work for very bad points
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
  // ===                  CORRESPONDENCES                 ===
  // ==========================================================

  if pl gt 1 then printf "\nComputing correspondences";  end if;

  // Want rho-1 independent `nice` correspondences.
  // Construct them using powers of Hecke operator
  mat_space := KMatrixSpace(QQ, 2*g, 2*g);
  q := IsZero(hecke_prime) select p else hecke_prime;
  correspondences, Tq := hecke_corr(data,q,N : basis0:=basis0,basis1:=basis1,printlevel:=pl);
  if pl gt 1 then printf "\nHecke operator at %o acting on H^1:\n%o\n", q, Tq; end if;
  if IsDiagonal(Tq) or Degree(CharacteristicPolynomial(Tq)) lt 2*g then
    error "p-Adic approximation of Hecke operator does not generate the endomorphism algebra. Please pick a different prime. ";
  end if;
  if #nice_correspondences gt 0 then 
    correspondences := nice_correspondences;
  else
    if q ne p then
      printf "\nWARNING: Using Hecke operator T_%o, but %o isn't our working prime %o.\n", q, q, p; 
    end if;  
    if Dimension(sub<mat_space | correspondences>) lt rho-1 then
      error "Powers of Hecke operator don't suffice to generate the space of nice correspondences";
    end if;
  end if;
    
  if pl gt 1 then printf "\nNice correspondences:\n%o\n\n", correspondences; end if;

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
  assert min_val_check_equiv ge Nend/2;
  //assert IsZero(big_split*Transpose(Tq) - Transpose(Tq)*big_split);     // Test equivariance
  if pl gt 1 then printf "\nequivariant splitting:\n%o\n", eqsplit; end if;

  F_lists := [* *]; // functions vanishing in rational points, one for each corresp
  zeroes_lists := [* *]; // zeroes of functions in F_lists; these are centered at 0, i.e. shifted 
  sols_lists := [* *]; // p-adic points corresponding to zeroes. 
  local_height_lists := [* *]; // local height as power series 
  E1_E2_lists := [* *]; // E1 tensor E2 as power series
  E1_lists := [* *]; 
  E2_lists := [* *]; 
  if #height_coeffs eq 0 or not use_log_basis then 
    heights := [* *];    // heights of auxiliary points. Different correspondences allowed (might cut down the # of necessary rational pts).
    E1P := 0;
    super_space := VectorSpace(Qp_small, g);
    E1_E2_subspace := sub<super_space | [Zero(super_space)]>;
    E1_E2_Ps := [* *]; // E1 tensor E2 of auxiliary points
  end if;


  for l := 1 to number_of_correspondences do
    //if #heights lt g or l le then 
    // There are still auxilliary heights to be computed or we want lots of functions
    Z := correspondences[l];

    // ==========================================================
    // ===                     HODGE                       ===
    // ==========================================================
    
    if pl gt 0 then printf  "\nComputing Hodge filtration for correspondence %o.\n", l; end if;

    if assigned betafil then delete betafil; end if;
    hodge_prec := 5; 
    repeat
      try
        eta,betafil,gammafil:=hodge_data(data,Z,bpt : prec := hodge_prec);
      catch e;
        hodge_prec +:= 5;
      end try;
    until assigned betafil;

    if pl gt 1 then 
      printf  "eta =  %o.\n", eta; 
      printf  "beta_fil  =  %o.\n", betafil; 
      printf  "gamma_fil =  %o.\n\n", gammafil; 
    end if;


    // ==========================================================
    // ===                  FROBENIUS                      ===
    // ==========================================================
     
    b0 := teichmueller_pt(bQ,data); 
    if pl gt 0 then printf  "Computing Frobenius structure for correspondence %o.\n", l; end if;
    b0pt := [QQ!c : c in xy_coordinates(b0, data)]; // xy-coordinates of P
    G := frob_struc(data,Z,eta, b0pt);
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


    if debug then
      // Comparison of the two parallel transport algorithms 
      // First computation of left multiplication in the algebra.
      PhiAZb_to_b02  := parallel_transport_from_b(bQ,Z,eta,data,local_base_point_index:prec:=prec,printlevel:=pl);
      // Second computation of left multiplication in the algebra.
      print " ";
      print "Parallel transport for base point was computed twice.";
      print "Their difference is: ", PhiAZb_to_b0 - PhiAZb_to_b02;
      print " ";
    end if;

    PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
    for i := 1 to numberofpoints do
      PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
        parallel_transport_to_z(Qppoints[i],Z,eta,data:prec:=prec)*PhiAZb[i]; // Now from b0 to Qppoints[i].
    end for;
     
    gammafil_list := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at all good points (0 if bad)
    gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 

    if pl gt 1 then printf  "Computing expansions of the filtration-respecting function gamma_fil.\n"; end if;
    for i := 1 to numberofpoints do
      if G_list[i] ne 0 then
        gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, N, 200);
        gammafil_list[i] := evalf0(ChangeRing(gammafil,LaurentSeriesRing(BaseRing(gammafil))),Qppoints[i],data);
      end if;
    end for;


    // ==========================================================
    // ===                  HEIGHTS                        ===
    // ==========================================================


    if #height_coeffs eq 0 or not use_log_basis then // Compute heights of auxiliary points.

      if IsZero(E1P) then  // Find a point with non-zero E1 to write down a basis of the Lie algebra. 
                           // To minimize precision loss, want small valuation of
                           // determinant of change of basis matrix.
        min_val_det := N;
        for j := 1 to #good_affine_rat_pts_xy_no_bpt do
          // local coordinate of the jth known ratl pt
          loc_coord := -Qppoints[ks[j]]`x + good_affine_rat_pts_xy_no_bpt[j][1]; 
          PhiAZb_j := PhiAZb_to_z[ks[j]]; // Frobenius structure
          E1j := Vector(Qp,g,[Evaluate(PhiAZb_j[i+1,1], loc_coord) : i in [1..g]]);
          basisH0star_j := [];
          for i := 0 to g-1 do
            // basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P)
            Append(~basisH0star_j, Eltseq(E1j*(ChangeRing(Tq_small,Qp)^i))); 
          end for; 
          val_det_j := Valuation(Determinant(Matrix(basisH0star_j)));
          if val_det_j lt min_val_det then
            // Better point found
            min_val_det := val_det_j; min_j := j; E1P := E1j;
            basisH0star := basisH0star_j;
          end if;
          //"val_det_j", val_det_j;
          if IsZero(val_det_j) then break; end if;
        end for;
        if min_val_det ge N then  // precision loss too high to obtain meaningful result.
          error "No good basis for H^0(Omega^1)^* generated by powers of iota(Tq) acting on E1(P) found";
        end if;
      end if; // IsZero(E1P)
      if pl gt 1 then printf "Using point %o at correspondence %o to generate the tangent space.\n", 
                                    good_affine_rat_pts_xy_no_bpt[min_j],l; end if;

    end if; //#height_coeffs eq 0 or not use_log_basis then 

    // heights contains the list of heights of auxiliary points
    if #height_coeffs eq 0 then // Compute heights of auxiliary points.
      if #heights lt g then  // add E1_E2(P) to known subspace until dimension is g.
        i := 1;
        repeat 
          loc_coord := - Qppoints[ks[i]]`x + good_affine_rat_pts_xy_no_bpt[i][1];
          // local coordinate of the ith known ratl pt P
          E1_E2_series := E1_tensor_E2(PhiAZb_to_z[ks[i]],betafil,basisH0star,data,Salpha);
          Kt := Parent(E1_E2_series);
          E1_E2_P := Qp_ext![Evaluate(c, loc_coord) : c in Eltseq(E1_E2_series)];
          new_E1_E2_subspace := E1_E2_subspace + sub<super_space | [super_space!Eltseq(E1_E2_P)]>;
          if Dimension(new_E1_E2_subspace) gt Dimension(E1_E2_subspace) then
            E1_E2_subspace := new_E1_E2_subspace; 
            if pl gt 1 then printf "Using point %o at correspondence %o to fit the height pairing.\n", good_affine_rat_pts_xy_no_bpt[i],l; end if;
            ht_series := height(PhiAZb_to_z[ks[i]],betafil,gammafil_listb_to_z[ks[i]],eqsplit,data); // height as power series
            Append(~heights, Evaluate(ht_series, loc_coord)); // height of A_Z(b, P)
            Append(~E1_E2_Ps, E1_E2_P);
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
          E1_E2_list[k] := E1_tensor_E2(PhiAZb_to_z[k],betafil,basisH0star,data,Salpha);
        end if;
      end if;
    end for;  // k := 1 to numberofpoints 
     
    Append(~local_height_lists, local_height_list);
    Append(~E1_E2_lists, E1_E2_list);
    Append(~E1_lists, E1_list);
    Append(~E2_lists, E2_list);

  end for; // l := 1 to number_of_correspondences 

  if #height_coeffs eq 0 and #heights lt g then
    error "Not enough rational points on the curve!"; // to span the symmetric square of the Mordell-Weil group";
  end if;

  if #height_coeffs eq 0 then 
    // Write the height pairing as a linear combination of the basis of symmetric bilinear
    // pairings dual to the E1_E2-basis of the auxiliary points. 
    E1_E2_Ps_matrix := Matrix([Eltseq(E1_E2) : E1_E2 in E1_E2_Ps]);
    heights_vector := Matrix(g,1,[ht : ht in heights]);
    height_coeffs := E1_E2_Ps_matrix^(-1)*heights_vector;
    // so the global height is of the form sum_i height_coeff[i]*Psi[i], where 
    // Psi[1],...,Psi[g] is the dual basis to E1_E2(P1),...,E1_E2(Pg)
  end if;

  for k := 1 to number_of_correspondences do

    F_list := [**];
    for l := 1 to numberofpoints do
      if G_list[l] eq 0 then
        F_list[l] := 0;
      else
        if use_log_basis then
          // now find the locally analytic function that extends the global height.
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
      printf "Power series expansions of the quadratic Chabauty functions at correspondence %o in all good affine disks, capped at precision %o\n", k, 3;  
      for i := 1 to #F_list do
        if F_list[i] ne 0 then 
        printf "disk %o\n expansion: %o \n\n", [Fp!(Qppoints[i]`x), Fp!(Qppoints[i]`b[2])], ChangePrecision(F_list[i], 3);
        end if;
      end for;
    end if; 
     
    Append(~F_lists, F_list);

    zero_list := [* *];
    sol_list  := [* *];
   

    // ==========================================================
    // ===                 FIND ZEROES                     ===
    // ==========================================================

    for i := 1 to numberofpoints do
      sol_list[i] := []; 
      zero_list[i] := []; 
      if G_list[i] ne 0 then
        Pp := Qppoints[i];
        xt, bt := local_coord(Pp,prec,data);
        // find affine local coordinates 
        W0invxt := Evaluate(W0^(-1), xt);
        b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
        yt := &+[W0invxt[2,j]*b_vector[j,1]:j in [1..Degree(Q)]];

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
              Append(~sol_list[i], [Qp_small!Evaluate(c, p*t) : c in [xt, yt]]);
            end for;
          end if;
        end for; // contrib in away_contributions
      end if; // G_list[i] ne 0
    end for;  // i:=1 to numberofpoints 

    Append(~zeroes_lists, zero_list);
    Append(~sols_lists, sol_list);
  end for;  // k := 1 to number_of_correspondences do

  // ==========================================================
  // ===                 SANITY CHECK                    ===
  // ==========================================================


  for i := 1 to number_of_correspondences do
    if pl gt 0 then printf "\n Sanity check at rational points for correspondence %o.  ", i; end if;
    F_list := F_lists[i]; 
    for j in [1..#good_Qpoints] do
      P := good_Qpoints[j]; 
      ind := FindQpointQp(P,Qppoints); 
      Pp := Qppoints[ind];
      vals := [];
      if ind gt 0 and (is_bad(Qppoints[ind],data) eq false) and (P`inf eq false) then		
        for contrib in away_contributions do
          Append(~vals,  Valuation(Qp_small!Evaluate(F_list[ind]-contrib,P`x - Pp`x))); 
        end for;
        // F_list[ind] = contrib for some away contribution contrib
        assert exists(v){ val : val in vals | val ge Nend/2};
        if pl gt 2 then  printf "\nThe valuations of the quadratic Chabauty function evaluated at (x,y) = %o minus the local constants coming heights away from %o are \n%o", p, good_affine_rat_pts_xy[j],  vals; end if;
      end if;
    end for;
  end for; //  i := 1 to number_of_correspondences 
  if pl gt 0 then  printf "\nSanity checks passed."; end if;

  // ==========================================================
  // ===               COMMON SOLUTIONS                  ===
  // ==========================================================

  if pl gt 2 then 
    for l := 1 to number_of_correspondences do 
      printf "\n\nThe list of solutions for the quadratic Chabauty function constructed from correspondence %o is \n %o \n\n", l, sols_lists[l]; 
    end for;
  end if;
  solutions := sols_lists[1];
  K := pAdicField(p, Nend);
  for i in [1..#Qppoints] do // residue disks
    if not IsEmpty(zeroes_lists[1,i]) then
      len := #zeroes_lists[1,i];
      if len gt 0 then 
        for j := 1 to len do // solutions for first correspondence
          P := sols_lists[1,i,j];  
          for l := 2 to number_of_correspondences do // correspondences
            match := [ ];
            for k := 1 to #zeroes_lists[l][i] do // solutions for lth correspondence
              R := sols_lists[l,i,k];
              min_val := Minimum([AbsolutePrecision(c) : c in P cat R])-1; 
              Append(~match, Min([Valuation(d) : d in [P[1]-R[1], P[2]-R[2]]]) ge min_val);
            end for;
            if not &or match then
              Exclude(~solutions[i], P);
            end if;
          end for;
        end for;
      end if;
    end if;
  end for; // i in [1..#Qppoints] 
  sols := &cat[L : L in solutions | #L gt 0];
  if pl gt 1 then printf "The common roots of the quadratic Chabauty functions in this affine patch are \n %o \n\n", sols; end if; 
  if pl gt 2 then printf "The lists of zeroes are \n %o \n", zeroes_lists; end if; 
  fake_rat_pts := [* *]; 
  for i := 1 to #sols do
    P := [lindepQp(sols[i,1]), lindepQp(sols[i,2])];
    if P notin good_affine_rat_pts_xy then
      if IsZero(eval_Q(Q, P[1], P[2])) then
        Append(~good_affine_rat_pts_xy, P); 
        if pl gt 1 then "Found rational point P", P; end if;
      else 
        Append(~fake_rat_pts, sols[i]); 
        if pl gt 1 then "Found (fake?) rational point P", sols[i]; end if;
      end if;
    else 
      if pl gt 1 then "Found rational point P", P; end if; 
    end if;
  end for;
  
  if #fake_rat_pts eq 0 then
    if pl gt 0 then 
      "\n\nThe curve has only the known rational points outside the bad residue disks and disks at infinity"; end if;
    return good_affine_rat_pts_xy, true, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints;
  else  
    if pl gt 0 then "\n\nThere are additional solutions that don't look rational."; end if;
    return good_affine_rat_pts_xy, false, bad_affine_rat_pts_xy, data, fake_rat_pts, bad_Qppoints;
  end if;

end function;



function hecke_operator_generates(S, p)
  // S is a space of cusp forms
  // Check that the Hecke operator Tp generates the Hecke algebra
  Tp := HeckeOperator(S, p);
  return not IsDiagonal(Tp) and Degree(MinimalPolynomial(Tp)) eq Dimension(S) div 2;
end function;



function QCModQuartic(Q, S : p := 5, bound := 100, N := 20, prec := 50, number_of_correspondences := 2, 
                printlevel := 0, known_pts := [], height_bd := 10^4, debug := false, base_point := 0)

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
      if pl gt 0 then 
        printf "\n Starting quadratic Chabauty computation for the affine patch \n %o = 0\n at the prime p = %o\n", Q, p;
      end if;
      try 
        good_pts1, bool1, bad_pts1, data1, fake_pts1, bad_disks1 := QCModAffine(Q, p : N := N, prec := prec, 
                 number_of_correspondences := number_of_correspondences, printlevel := printlevel, debug := debug, base_point := base_point);
        if not bool1 then continue; end if;
      catch e
      e;
        if pl gt 0 then printf "\n Error in qc computation at p = %o\n", p; end if;
        if pl gt 1 then e; end if;
        continue;
      end try;
      // Find a good second affine patch so that
      // - every residue disk is good (i.e. is affine and the Frobenius lift is defined
      //   there) on at least one affine patch
      // - every affine patch contains enough rational points to fit the height pairing.

      if pl gt 0 then 
        printf "\n Find a good second affine patch"; // so that the lift of Frobenius is defined for every point on at least one affine patch.";
      end if;
      Q_inf, A := second_affine_patch(Q, p : printlevel := printlevel, bd := 3);
      try
        if pl gt 0 then 
          printf "\n Starting quadratic Chabauty computation for the affine patch \n %o = 0\n at the prime p = %o\n", Q_inf, p;
        end if;
        good_pts2, bool2, bad_pts2, data2, fake_pts2, bad_disks2 := QCModAffine(Q_inf, p : N := N, prec := prec, 
                   number_of_correspondences := number_of_correspondences, printlevel := printlevel, debug := debug);
        if not bool2 then continue; end if;
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
      for P in Cpts do
        if P notin known_pts then continue; end if;
      end for;
      return true, p, Q_inf, Cpts;  
    end if; // (not IsDivisibleBy(Level(S), p)) and hecke_operator_generates(S, p) 

  end while;
  return false; 
end function;


