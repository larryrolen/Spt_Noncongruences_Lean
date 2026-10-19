import blessed.SptCM.Analytic.Repaired.Grid
import blessed.SptCM.Analytic.Repaired.WeilGenerators
import blessed.SptCM.Analytic.DualityPairing
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The actual auxiliary form, the published grid, and coefficient duality

The external boundary in this module is a general multiplication theorem for
the two modular-form spaces.  It says that multiplication preserves the
analytic qualifications, adds the weights to two, and that Fourier
coefficients multiply by convolution.  It contains neither the specialized
three-term constant coefficient nor coefficient duality.  Those are proved
below from the internally constructed `auxiliaryForm`, its coefficients, and
the published Ahlgren--Kim grid.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic
open scoped BigOperators

/-- A general E4 multiplication/residue interface for the eta--j space and
Ahlgren--Kim's grid space.  `coefficient_zero` is the ordinary Cauchy product
formula for two Laurent expansions once lower bounds are supplied. -/
structure WeightTwoMultiplicationTheory
    (K Form Product : Type*) [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (G : AhlgrenKimGridTheorem K) where
  product : Form → QSeries K → Product
  coefficients : Product → HForm K
  IsWeaklyHolomorphic : Product → Prop
  IsWeightTwo : Product → Prop
  constantTerm : Product → K
  constantTerm_eq_coefficient_zero : ∀ F,
    constantTerm F = coefficients F 0
  product_is_weaklyHolomorphic : ∀ A m B,
    E.qualifies A → G.Qualifies m B →
      IsWeaklyHolomorphic (product A B)
  product_is_weightTwo : ∀ A m B,
    E.qualifies A → G.Qualifies m B →
      IsWeightTwo (product A B)
  coefficient_zero : ∀ A B lo hi,
    (∀ r, r < lo → E.coefficients A r = 0) →
    (∀ r, r < -hi → B r = 0) →
    coefficients (product A B) 0 =
      ∑ r ∈ Finset.Icc lo hi, (E.coefficients A r : K) * B (-r)
  residueTheorem : ∀ F,
    IsWeaklyHolomorphic F → IsWeightTwo F → constantTerm F = 0

/-- The integral Fourier expansion of the actual eta--j auxiliary form,
viewed over a field. -/
noncomputable def actualAuxiliarySeries
    {K Form : Type*} [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (k : ℕ) (a : ℤ) : HForm K :=
  fun r => (auxiliaryHn E.toEtaJPowerBasis k a r : K)

lemma actualAuxiliarySeries_normalization
    {K Form : Type*} [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (k : ℕ) (hk : 0 < k) (a : ℤ) :
    HasHnNormalization (24 * k - 1) (a : K)
      (actualAuxiliarySeries E k a) := by
  have h := auxiliaryHn_normalization E.toEtaJPowerBasis k hk a
  refine ⟨?_, ?_, ?_⟩
  · simpa [actualAuxiliarySeries] using congrArg (fun z : ℤ => (z : K)) h.1
  · simpa [actualAuxiliarySeries] using congrArg (fun z : ℤ => (z : K)) h.2.1
  · intro r hr hrn hr1
    simp [actualAuxiliarySeries, h.2.2 r hr hrn hr1]

lemma actualAuxiliarySeries_lower_bound
    {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (k : ℕ) (hk : 0 < k) (a : ℤ)
    (r : ℤ) (hr : r < -((24 * k - 1 : ℕ) : ℤ)) :
    E.coefficients (auxiliaryForm E.toEtaJPowerBasis k a) r = 0 := by
  have hnorm := auxiliaryHn_normalization E.toEtaJPowerBasis k hk a
  exact hnorm.2.2 r (by omega) (by omega) (by omega)

lemma gridSeries_lower_bound
    {K : Type*} [Field K] (G : AhlgrenKimGridTheorem K)
    (m : ℕ) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (r : ℤ) (hr : r < -((m : ℤ) ^ 2)) :
    G.grid m r = 0 := by
  have hpp := G.principalPart m hm hm6 r
  rw [hpp (by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
    nlinarith [sq_pos_of_pos hmpos])]
  have hsq : (1 : ℤ) < (m : ℤ) ^ 2 := by
    have hmz : (1 : ℤ) < m := by exact_mod_cast hm
    nlinarith
  simp [show r ≠ -((m : ℤ) ^ 2) by omega,
    show r ≠ -1 by omega]

/-- Pure coefficient bookkeeping: with the two paper normalizations, the
constant Cauchy coefficient has exactly the three displayed terms. -/
lemma normalized_constant_convolution
    {K : Type*} [Field K] {n m : ℕ} {a : K}
    {chi : ℕ → K} {H Gs : HForm K}
    (hn : 0 < n) (hm : 1 < m)
    (hnorm : HasHnNormalization n a H)
    (hgrid : HasGridPrincipalPart chi m Gs) :
    (∑ r ∈ Finset.Icc (-(n : ℤ)) ((m : ℤ) ^ 2), H r * Gs (-r)) =
      normalizedProductConstantTerm n m H Gs := by
  classical
  let s : Finset ℤ := Finset.Icc (-(n : ℤ)) ((m : ℤ) ^ 2)
  have hmpos : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsneg : -(n : ℤ) ∈ s := by simp [s]; nlinarith
  have hsone : (1 : ℤ) ∈ s := by simp [s]; nlinarith [sq_pos_of_pos hmpos]
  have hssq : ((m : ℤ) ^ 2) ∈ s := by simp [s]; nlinarith
  have hneg_one : (-(n : ℤ)) ≠ 1 := by omega
  have hneg_sq : (-(n : ℤ)) ≠ (m : ℤ) ^ 2 := by nlinarith [sq_pos_of_pos hmpos]
  have hone_sq : (1 : ℤ) ≠ (m : ℤ) ^ 2 := by nlinarith
  have hterm : ∀ r ∈ s, H r * Gs (-r) =
      if r = -(n : ℤ) then H (-(n : ℤ)) * Gs n
      else if r = 1 then H 1 * Gs (-1)
      else if r = (m : ℤ) ^ 2 then
        H ((m : ℤ) ^ 2) * Gs (-((m : ℤ) ^ 2))
      else 0 := by
    intro r hrs
    by_cases hrn : r = -(n : ℤ)
    · subst r; simp
    by_cases hr1 : r = 1
    · subst r
      simp [show (1 : ℤ) ≠ -(n : ℤ) by omega]
    by_cases hrm : r = (m : ℤ) ^ 2
    · subst r
      simp [show ((m : ℤ) ^ 2) ≠ -(n : ℤ) by nlinarith,
        show ((m : ℤ) ^ 2) ≠ 1 by nlinarith]
    simp only [hrn, hr1, hrm, ↓reduceIte]
    by_cases hr25 : r < 25
    · rw [hnorm.2.2 r hr25 hrn hr1, zero_mul]
    · have hrpos : 0 < r := by omega
      have hg := hgrid (-r) (by omega)
      have hnotm : -r ≠ -((m : ℤ) ^ 2) := by omega
      have hnot1 : -r ≠ -1 := by omega
      simp [hnotm, hnot1] at hg
      rw [hg, mul_zero]
  rw [show (∑ r ∈ Finset.Icc (-(n : ℤ)) ((m : ℤ) ^ 2), H r * Gs (-r)) =
      ∑ r ∈ s, H r * Gs (-r) by rfl]
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∀ r ∈ s,
      (if r = -(n : ℤ) then H (-(n : ℤ)) * Gs n
       else if r = 1 then H 1 * Gs (-1)
       else if r = (m : ℤ) ^ 2 then
         H ((m : ℤ) ^ 2) * Gs (-((m : ℤ) ^ 2)) else 0) =
      (if r = -(n : ℤ) then H (-(n : ℤ)) * Gs n else 0) +
      (if r = 1 then H 1 * Gs (-1) else 0) +
      (if r = (m : ℤ) ^ 2 then
         H ((m : ℤ) ^ 2) * Gs (-((m : ℤ) ^ 2)) else 0) := by
    intro r _
    by_cases hrn : r = -(n : ℤ)
    · subst r; simp [hneg_one, hneg_sq]
    by_cases hr1 : r = 1
    · subst r
      simp [show (1 : ℤ) ≠ -(n : ℤ) by omega, hone_sq]
    by_cases hrm : r = (m : ℤ) ^ 2
    · subst r
      simp [show ((m : ℤ) ^ 2) ≠ -(n : ℤ) by nlinarith,
        show ((m : ℤ) ^ 2) ≠ 1 by nlinarith]
    simp [hrn, hr1, hrm]
  rw [Finset.sum_congr rfl hsplit]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' s (-(n : ℤ)),
    Finset.sum_ite_eq' s (1 : ℤ),
    Finset.sum_ite_eq' s ((m : ℤ) ^ 2)]
  simp [hsneg, hsone, hssq, normalizedProductConstantTerm]

/-- I08: multiplication of the actual `η P_k(j)` by the actual published grid
form is weakly holomorphic of weight two, and direct Cauchy multiplication
gives precisely the normalized three-term constant coefficient. -/
theorem actual_product_weight_two
    {K Form Product : Type*} [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (G : AhlgrenKimGridTheorem K)
    (R : WeightTwoMultiplicationTheory K Form Product E G)
    (k m : ℕ) (hk : 0 < k) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (a : ℤ) :
    R.IsWeaklyHolomorphic
        (R.product (auxiliaryForm E.toEtaJPowerBasis k a) (G.grid m)) ∧
      R.IsWeightTwo
        (R.product (auxiliaryForm E.toEtaJPowerBasis k a) (G.grid m)) ∧
      R.coefficients
          (R.product (auxiliaryForm E.toEtaJPowerBasis k a) (G.grid m)) 0 =
        normalizedProductConstantTerm (24 * k - 1) m
          (actualAuxiliarySeries E k a) (G.grid m) := by
  let A := auxiliaryForm E.toEtaJPowerBasis k a
  have hA := auxiliaryForm_qualifies E.toEtaJPowerBasis k a
  have hG := G.qualifies_grid m hm hm6
  refine ⟨R.product_is_weaklyHolomorphic A m (G.grid m) hA hG,
    R.product_is_weightTwo A m (G.grid m) hA hG, ?_⟩
  rw [R.coefficient_zero A (G.grid m)
    (-((24 * k - 1 : ℕ) : ℤ)) ((m : ℤ) ^ 2)
    (actualAuxiliarySeries_lower_bound E k hk a)
    (gridSeries_lower_bound G m hm hm6)]
  exact normalized_constant_convolution (by omega) hm
    (actualAuxiliarySeries_normalization E k hk a)
    (G.principalPart m hm hm6)

/-- E4's residue theorem applied to the genuine product, with the exact
constant coefficient established by `actual_product_weight_two`. -/
theorem actual_weightTwoResidue
    {K Form Product : Type*} [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (G : AhlgrenKimGridTheorem K)
    (R : WeightTwoMultiplicationTheory K Form Product E G)
    (k m : ℕ) (hk : 0 < k) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (a : ℤ) :
    WeightTwoResidueInput (24 * k - 1) m
      (actualAuxiliarySeries E k a) (G.grid m) := by
  have hp := actual_product_weight_two E G R k m hk hm hm6 a
  rw [WeightTwoResidueInput, ← hp.2.2,
    ← R.constantTerm_eq_coefficient_zero]
  exact R.residueTheorem _ hp.1 hp.2.1

/-- I08 coefficient duality for the internally constructed auxiliary form and
the actual published grid. -/
theorem actual_coefficient_duality
    {K Form Product : Type*} [Field K] [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (G : AhlgrenKimGridTheorem K)
    (R : WeightTwoMultiplicationTheory K Form Product E G)
    (k m : ℕ) (hk : 0 < k) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (a : ℤ) :
    actualAuxiliarySeries E k a ((m : ℤ) ^ 2) =
      -G.grid m ((24 * k - 1 : ℕ) : ℤ) - (chi12 m : K) * (a : K) := by
  rw [← G.chi_eq_chi12 m]
  exact coefficient_duality_of_weightTwoResidue hm
    (actualAuxiliarySeries_normalization E k hk a)
    (G.principalPart m hm hm6)
    (actual_weightTwoResidue E G R k m hk hm hm6 a)

/-- The genuine `m > 1` inert square-coefficient endpoint. -/
theorem actual_Hn_square_coefficient_eq_zero_of_canonical_inert
    (ℓ k m : ℕ) [Fact ℓ.Prime]
    {Form Product : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form)
    (G : AhlgrenKimGridTheorem (ZMod ℓ))
    (R : WeightTwoMultiplicationTheory (ZMod ℓ) Form Product E G)
    (hk : 0 < k)
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-((24 * k - 1 : ℕ) : ℤ)) = -1)
    (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (hgridCycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (G.grid m) =
      thetaCycleEigenvalue ℓ • G.grid m) :
    actualAuxiliarySeries (K := ZMod ℓ) E k (aCoeff ((24 * k - 1 : ℕ) : ℤ)) ((m : ℤ) ^ 2) = 0 := by
  exact Hn_square_coefficient_eq_zero_of_canonical_inert
    ℓ (24 * k - 1) m
    (actualAuxiliarySeries E k (aCoeff ((24 * k - 1 : ℕ) : ℤ)))
    (G.grid m) G.chi hcanonical hAK hEuler hinert hm
    (actualAuxiliarySeries_normalization E k hk (aCoeff ((24 * k - 1 : ℕ) : ℤ)))
    (G.principalPart m hm hm6)
    (actual_weightTwoResidue E G R k m hk hm hm6
      (aCoeff ((24 * k - 1 : ℕ) : ℤ))) hgridCycle

/-- The separately normalized `m = 1` endpoint for the same actual form. -/
theorem actual_Hn_first_coefficient_eq_zero_of_canonical_inert
    (ℓ k : ℕ) [Fact ℓ.Prime]
    {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (hk : 0 < k)
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-((24 * k - 1 : ℕ) : ℤ)) = -1) :
    actualAuxiliarySeries (K := ZMod ℓ) E k (aCoeff ((24 * k - 1 : ℕ) : ℤ)) 1 = 0 := by
  exact Hn_first_coefficient_eq_zero_of_canonical_inert
    ℓ (24 * k - 1) (actualAuxiliarySeries E k (aCoeff ((24 * k - 1 : ℕ) : ℤ)))
    hcanonical hAK hEuler hinert
    (actualAuxiliarySeries_normalization E k hk (aCoeff ((24 * k - 1 : ℕ) : ℤ)))

end SptCM.Analytic.Repaired
