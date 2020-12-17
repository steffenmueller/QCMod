This is Magma code to carry out quadratic Chabauty for curves of genus > 1 over the
rationals satisfying the following conditions
* rank = genus
* real multiplication
* enough rational points on the curve to solve for the height pairing, unless the genus is 2.

The theory is described in `Quadratic Chabauty for modular curves: Algorithms and
Examples` and `Explicit Chabauty-Kim for the Split Cartan Modular Curve of Level 13`
by J.S. Balakrishnan, N. Dogra, J.S. Müller, J. Tuitman and J. Vonk.

Most of the code consists of wrappers around a slightly modified earlier version, mostly
written by Jan Tuitman and based on even earlier
SAGE code by Netan Dogra; the latter was hardcoded for the computations
in `Explicit Chabauty-Kim for the Split Cartan Modular Curve of Level 13`. 
Also includes contributions by Jennifer Balakrishnan and Jan Vonk, as well as code due to
Michael Stoll.


List of files:
-- qc_modular.m: Contains
   - QCModAffine: Main function, takes a plane affine curve (not necessarily
      singular) with integer coefficients, monic in y, and a prime p and outputs the rational points 
      in those disks where Tuitman's Frobenius lift is defined. Also outputs additional information, such 
      as additional p-adic solutions which don't look rational.
      Includes numerous optional arguments
   - QCModQuartic: takes an integer polynomial defining an affine patch of a smooth plane quartic
      and outputs the rational points.
-- divisor_heights.m: Contains the function local_cg_height, which computes the local height pairing
    between two divisors with disjoint support on an odd degree hyperelliptic curve (with
    various restrictions) using construction of Coleman-Gross. Essentially ports earlier Sage code due to 
    Jennifer Balakrishnan, based on Balakrishnan-Besser, `Coleman-Gross height pairings and the p-adic
    sigma function`, IMRN 2012
-- MWgroupg2: Code due to Michael Stoll to compute generators for the
    Mordell-Weil group of the Jacobian of a genus 2 curve, based on Müller-Stoll,
    `Canonical heights on genus two Jacobians`, A&NT 2016.
    Not needed for versions >= 2.25 of magma.
-- mws-qc.m: Implementation of the Mordell-Weil sieve based on an earlier
    version of Magma's Mordell-Weil sieve due to Michael Stoll, adapted for use in combination
    with quadratic Chabauty.  
-- hodge.m: Computes the Hodge filtration using the algorithm described in section 4 of 
    `Explicit Chabauty-Kim for the Split Cartan Modular Curve of Level 13`
-- frobenius.m: Computes the Frobenius structure using the algorithm described in section 4 of 
    `Explicit Chabauty-Kim for the Split Cartan Modular Curve of Level 13`
-- heights.m: Computes Nekovar heights as described in 
    `Explicit Chabauty-Kim for the Split Cartan Modular Curve of Level 13` and various
    related functions.
-- hecke_correspondence.m: Computes a Hecke operator using Eichler-Shimura and nice
    correspondences. 
-- howe-zhu: Implements the criterion of Howe-Zhu, `On the existence of
    absolutely simple abelian varieties of a given dimension over an arbitrary field`,
    JNT 2002,  to show that abelian varieties are absolutely simple.
-- symplectic_basis.m: Given a basis of H^1_dR of a smooth projective curve such that the
    first g elements generate regular differentials, computes the cup product and a
    symplectic basis with respect to the cup product.
-- second_patch_quartic.m: Given an affine patch of a smooth plane quartic, finds a second
    patch so that running quadratic Chabauty on both suffices to provably find the rational
    points on the projective model.
-- misc.m: various functions, such as an implementation of rational reconstruction of p-adic
    numbers using LLL, rank computations using Kolyvagin-Logachev, equivariant splittings of
    the Hodge filtration of H^1 and coefficients mod p^N of p-adic points under Abel-Jacobi in
    terms of generators.
-- qc_init_g2.m: Contains several functions necessary for quadratic Chabauty in genus 2
    -- find_qc_primes: computes primes for combination of QC and the MWS
    -- generators: computes generators of the Mordell-Weil group
    -- height_init_g2: computes divisors suitable to solve for the height pairing using
        local_CG_heights for local heights at p and intersections for local heights away
        from p.
-- applications.m, auxpolys.m, coho.m, coleman.m, froblift.m, reductions.m, singleintegrals.m: 
    Due to Jan Tuitman, computes Frobenius lifts and  Coleman integrals, based on 
      - Tuitman, `Counting points on curves using a map to P1`, Math. Comp. 2016
      - Tuitman, `Counting points on curves using a map to P1, II`, Finite Fields Appl, 2017
      - Balakrishnan-Tuitman, `Jennifer S. Balakrishnan and Jan Tuitman. Explicit Coleman
        integration for curves`, Math. Comp., to appear,
    with some minor modifications.  
-- Examples: Contains code and log files for the examples described in our two papers. To
    run the code, copy it into the top level folder.


If you have questions or suggestions or if you find bugs, let me know.

Steffen Müller, Rijksuniversiteit Groningen
steffen.muller@rug.nl

