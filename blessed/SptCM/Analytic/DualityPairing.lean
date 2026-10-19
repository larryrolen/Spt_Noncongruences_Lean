import blessed.SptCM.Analytic.PaperCoefficientModels
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

/-!
# Coefficient duality, regularized pairing, and class-polynomial bookkeeping

This module formalizes the algebraic and limiting deductions in Sections 3 and
4.  Analytic statements cited from the literature are not installed as axioms:
they are named proposition-valued inputs to the relevant theorems.  In
particular, the Stokes argument is represented by its finite-height identity
and the two limits actually used in passing to the regularized pairing.
-/

namespace SptCM.Analytic

open Filter Polynomial
open scoped Topology BigOperators


/-- Coefficient model for the auxiliary weakly holomorphic form `H_n`. -/
abbrev HForm (R : Type*) := ℤ → R

/-- The exact Fourier normalization
`H_n = q^{-n/24} - a(n) q^{1/24} + O(q^{25/24})`. -/
def HasHnNormalization {R : Type*} [Ring R]
    (n : ℕ) (a : R) (H : HForm R) : Prop :=
  H (-(n : ℤ)) = 1 ∧ H 1 = -a ∧
    ∀ r : ℤ, r < 25 → r ≠ -(n : ℤ) → r ≠ 1 → H r = 0

/-- A chosen auxiliary coefficient series; no unformalized modularity assertion
is built into the definition. -/
def auxiliaryHForm {R : Type*} (H : HForm R) : HForm R := H

/-- The two coefficient statements extracted from the chosen normalization. -/
theorem Hn_normalization_coefficients
    {R : Type*} [Ring R] {n : ℕ} {a : R} {H : HForm R}
    (h : HasHnNormalization n a H) :
    H (-(n : ℤ)) = 1 ∧ H 1 = -a :=
  ⟨h.1, h.2.1⟩

/-- The three possibly nonzero summands in the constant coefficient of
`H_n G_m`.  The normalizations of `H_n` and `G_m` show that every other
pair of opposite Fourier exponents contributes zero. -/
def normalizedProductConstantTerm {R : Type*} [Ring R]
    (n m : ℕ) (H G : HForm R) : R :=
  H (-(n : ℤ)) * G n + H 1 * G (-1) +
    H ((m : ℤ) ^ 2) * G (-((m : ℤ) ^ 2))

/-- The residue-theorem input used in coefficient duality, stated before
coefficient comparison: a weight-two weakly holomorphic product on `X(1)` has
zero constant coefficient.  Here the constant coefficient is represented by
the three terms left by the two explicit principal-part normalizations. -/
def WeightTwoResidueInput {R : Type*} [Ring R]
    (n m : ℕ) (H G : HForm R) : Prop :=
  normalizedProductConstantTerm n m H G = 0

/-- Coefficient comparison after the residue theorem.  This derives the
constant-term identity consumed by coefficient duality from:

* the normalization of `H_n`,
* the principal part of the canonical grid form `G_m`, and
* the cited weight-two residue theorem for their product.

Thus the duality identity itself is not assumed as an input. -/
theorem constantTerm_identity_of_weightTwoResidue
    {R : Type*} [CommRing R] {n m : ℕ} {a : R}
    {chi : ℕ → R} {H G : HForm R}
    (hm : 1 < m)
    (hnorm : HasHnNormalization n a H)
    (hgrid : HasGridPrincipalPart chi m G)
    (hresidue : WeightTwoResidueInput n m H G) :
    G n + H ((m : ℤ) ^ 2) - chi m * H 1 = 0 := by
  have hmneg : -((m : ℤ) ^ 2) < 0 := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
    nlinarith [sq_pos_of_pos hmpos]
  have hgrid_m : G (-((m : ℤ) ^ 2)) = 1 := by
    simpa using hgrid (-((m : ℤ) ^ 2)) hmneg
  have hm_sq_ne_one : (m : ℤ) ^ 2 ≠ 1 := by
    nlinarith
  have hgrid_one : G (-1) = -chi m := by
    have hne : (-1 : ℤ) ≠ -((m : ℤ) ^ 2) := by
      intro h
      apply hm_sq_ne_one
      omega
    simpa [hne] using hgrid (-1) (by norm_num)
  rw [WeightTwoResidueInput, normalizedProductConstantTerm,
    hnorm.1, hgrid_m, hgrid_one] at hresidue
  linear_combination hresidue

/-- The constant-term computation in the proof of coefficient duality. -/
theorem coefficient_duality
    {R : Type*} [CommRing R] {a b hOne hSquare chi : R}
    (hone : hOne = -a)
    (hconstant : b + hSquare - chi * hOne = 0) :
    hSquare = -b - chi * a := by
  rw [hone] at hconstant
  linear_combination hconstant

/-- The coefficient-duality formula with its residue-theorem derivation made
explicit. -/
theorem coefficient_duality_of_weightTwoResidue
    {R : Type*} [CommRing R] {n m : ℕ} {a : R}
    {chi : ℕ → R} {H G : HForm R}
    (hm : 1 < m)
    (hnorm : HasHnNormalization n a H)
    (hgrid : HasGridPrincipalPart chi m G)
    (hresidue : WeightTwoResidueInput n m H G) :
    H ((m : ℤ) ^ 2) = -G n - chi m * a := by
  exact coefficient_duality (Hn_normalization_coefficients hnorm).2
    (constantTerm_identity_of_weightTwoResidue hm hnorm hgrid hresidue)

/-- The mod-`ℓ` square-coefficient vanishing is the immediate consequence of
coefficient duality and the two theta-cycle vanishings. -/
theorem square_coefficient_eq_zero_of_duality
    {R : Type*} [CommRing R] {a b hSquare chi : R}
    (hduality : hSquare = -b - chi * a)
    (ha : a = 0) (hb : b = 0) :
    hSquare = 0 := by
  simp [hduality, ha, hb]

/-- The complete normalization-to-vanishing deduction used for `H_n`.
Unlike a bundled “duality component”, the hypotheses expose exactly the
constant-term identity and the two independently obtained coefficient
vanishings. -/
theorem Hn_square_coefficient_eq_zero
    {R : Type*} [CommRing R] {n m : ℕ} {a b chi : R} {H : HForm R}
    (hnorm : HasHnNormalization n a H)
    (hconstant : b + H ((m : ℤ) ^ 2) - chi * H 1 = 0)
    (ha : a = 0) (hb : b = 0) :
    H ((m : ℤ) ^ 2) = 0 := by
  have hone : H 1 = -a := (Hn_normalization_coefficients hnorm).2
  have hduality : H ((m : ℤ) ^ 2) = -b - chi * a :=
    coefficient_duality hone hconstant
  exact square_coefficient_eq_zero_of_duality hduality ha hb

/-- The complete `m > 1` square-coefficient vanishing argument at an inert
index.  The mock coefficient vanishes by exact canonical `U_ℓ`-vanishing and
the cited Ahlgren--Kim theta-cycle implication; the grid coefficient vanishes
by its already-established theta support and the same Euler mismatch; and the
weight-two residue theorem supplies coefficient duality. -/
theorem Hn_square_coefficient_eq_zero_of_canonical_inert
    (ℓ n m : ℕ) [Fact ℓ.Prime]
    (H G : HForm (ZMod ℓ)) (chi : ℕ → ZMod ℓ)
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1)
    (hm : 1 < m)
    (hnorm : HasHnNormalization n (aCoeff n : ZMod ℓ) H)
    (hgrid : HasGridPrincipalPart chi m G)
    (hresidue : WeightTwoResidueInput n m H G)
    (hgridCycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) G =
      thetaCycleEigenvalue ℓ • G) :
    H ((m : ℤ) ^ 2) = 0 := by
  have ha : (aCoeff n : ZMod ℓ) = 0 :=
    aCoeff_mod_eq_zero_of_canonical_inert_exact ℓ n
      hcanonical hAK hEuler hinert
  have hb : G n = 0 :=
    gridCoeff_eq_zero_of_inert ℓ G n hgridCycle hEuler hinert
  have hduality :
      H ((m : ℤ) ^ 2) = -G n - chi m * (aCoeff n : ZMod ℓ) :=
    coefficient_duality_of_weightTwoResidue hm hnorm hgrid hresidue
  exact square_coefficient_eq_zero_of_duality hduality ha hb

/-- The `m = 1` endpoint used separately in the paper. -/
theorem first_coefficient_eq_zero
    {R : Type*} [Ring R] {a hOne : R}
    (hone : hOne = -a) (ha : a = 0) : hOne = 0 := by
  simp [hone, ha]

/-- The endpoint `m = 1`: the normalized coefficient `H_n(1)` is the
negative mock coefficient, so the same exact canonical theta argument makes
it vanish. -/
theorem Hn_first_coefficient_eq_zero_of_canonical_inert
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (H : HForm (ZMod ℓ))
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1)
    (hnorm : HasHnNormalization n (aCoeff n : ZMod ℓ) H) :
    H 1 = 0 := by
  apply first_coefficient_eq_zero (Hn_normalization_coefficients hnorm).2
  exact aCoeff_mod_eq_zero_of_canonical_inert_exact ℓ n
    hcanonical hAK hEuler hinert

/-- Data exposed by the truncated Stokes computation.  `bulk T` is the
truncated integral and `error T` is the nonholomorphic boundary contribution.
The cited shadow formula enters only through the displayed finite-height
identity, rather than through an assumed final pairing formula. -/
structure StokesPairingData where
  scale : ℝ
  pairing : ℝ
  constantTerm : ℝ
  bulk : ℕ → ℝ
  error : ℕ → ℝ
  bulk_tendsto : Tendsto bulk atTop (𝓝 pairing)
  error_tendsto : Tendsto error atTop (𝓝 0)
  finite_height_identity : ∀ T, scale * bulk T = constantTerm + error T


/-- The regularized Petersson pairing represented by the limit field of the
Stokes data. -/
def regularizedPairing (d : StokesPairingData) : ℝ := d.pairing

/-- Passing to the limit in the truncated Stokes identity gives the pairing
formula from Section 3. -/
theorem StokesPairingData.pairing_formula (d : StokesPairingData) :
    d.scale * d.pairing = d.constantTerm := by
  have hleft : Tendsto (fun T => d.scale * d.bulk T) atTop
      (𝓝 (d.scale * d.pairing)) :=
    tendsto_const_nhds.mul d.bulk_tendsto
  have hright : Tendsto (fun T => d.constantTerm + d.error T) atTop
      (𝓝 (d.constantTerm + 0)) :=
    tendsto_const_nhds.add d.error_tendsto
  have hleft' : Tendsto (fun T => d.constantTerm + d.error T) atTop
      (𝓝 (d.scale * d.pairing)) := by
    simpa only [d.finite_height_identity] using hleft
  have := tendsto_nhds_unique hleft' hright
  simpa using this

/-- If the product constant term is zero and the shadow normalization is
nonzero, the regularized inner product vanishes. -/
theorem StokesPairingData.pairing_eq_zero
    (d : StokesPairingData) (hscale : d.scale ≠ 0)
    (hconstant : d.constantTerm = 0) :
    d.pairing = 0 := by
  have hprod : d.scale * d.pairing = 0 := by
    rw [d.pairing_formula, hconstant]
  exact (mul_eq_zero.mp hprod).resolve_left hscale

/-- The final `H_n` orthogonality deduction: its two constant-term
contributions cancel, so the nonzero shadow scale forces the pairing to be
zero. -/
theorem Hn_pairing_eq_zero
    (d : StokesPairingData) (hscale : d.scale ≠ 0)
    {a : ℝ} (hconstant : d.constantTerm = a - a) :
    regularizedPairing d = 0 := by
  apply d.pairing_eq_zero hscale
  simpa using hconstant

/-- The precisely cited Weyl-vector formula of Bruinier--Schwagenscheidt,
packaged as a proposition rather than a global axiom. -/
def BruinierSchwagenscheidtWeylInput
    (weylVector factor pairing : ℝ) : Prop :=
  weylVector = factor * pairing

/-- Vanishing of the regularized pairing forces all Weyl exponents supplied by
that cited formula to vanish. -/
theorem weylVector_eq_zero_of_pairing_eq_zero
    {weylVector factor pairing : ℝ}
    (hBS : BruinierSchwagenscheidtWeylInput weylVector factor pairing)
    (hpairing : pairing = 0) :
    weylVector = 0 := by
  simp [BruinierSchwagenscheidtWeylInput, hpairing] at hBS
  exact hBS

section ClassPolynomials

variable {R ι κ : Type*} [CommRing R]

/-- The root-product construction used for each oriented CM class set. -/
noncomputable def rootPolynomial (s : Finset ι) (value : ι → R) : Polynomial R :=
  ∏ i ∈ s, (X - C (value i))

/-- A class polynomial defined as a finite product of linear factors is monic. -/
theorem rootPolynomial_monic (s : Finset ι) (value : ι → R) :
    (rootPolynomial s value).Monic := by
  exact monic_prod_X_sub_C value s

/-- Its degree is the number of CM classes in the indexing set. -/
theorem rootPolynomial_natDegree [Nontrivial R]
    (s : Finset ι) (value : ι → R) :
    (rootPolynomial s value).natDegree = s.card := by
  exact natDegree_finsetProd_X_sub_C_eq_card s value

/-- Combining the two orientations used for `A_n` (or for `B_n`). -/
noncomputable def twoOrientationClassPolynomial
    (s : Finset ι) (t : Finset κ) (u : ι → R) (v : κ → R) : Polynomial R :=
  rootPolynomial s u * rootPolynomial t v

/-- The two-orientation class polynomial is monic. -/
theorem twoOrientationClassPolynomial_monic
    (s : Finset ι) (t : Finset κ) (u : ι → R) (v : κ → R) :
    (twoOrientationClassPolynomial s t u v).Monic := by
  exact (rootPolynomial_monic s u).mul (rootPolynomial_monic t v)

/-- Its degree is the sum of the two oriented class counts. -/
theorem twoOrientationClassPolynomial_natDegree [Nontrivial R]
    (s : Finset ι) (t : Finset κ) (u : ι → R) (v : κ → R) :
    (twoOrientationClassPolynomial s t u v).natDegree = s.card + t.card := by
  rw [twoOrientationClassPolynomial,
    (rootPolynomial_monic s u).natDegree_mul (rootPolynomial_monic t v),
    rootPolynomial_natDegree, rootPolynomial_natDegree]

/-- If each orientation contains `h` ideal classes, the degree is `2h`, exactly
as in the paper's integral-coordinate lemma. -/
theorem twoOrientationClassPolynomial_natDegree_eq_two_mul [Nontrivial R]
    (s : Finset ι) (t : Finset κ) (u : ι → R) (v : κ → R)
    {h : ℕ} (hs : s.card = h) (ht : t.card = h) :
    (twoOrientationClassPolynomial s t u v).natDegree = 2 * h := by
  rw [twoOrientationClassPolynomial_natDegree, hs, ht]
  omega

end ClassPolynomials

end SptCM.Analytic
