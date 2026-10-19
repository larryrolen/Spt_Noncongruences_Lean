import blessed.SptCM.Analytic.Repaired.CharacteristicGridSupport
import blessed.SptCM.Analytic.Repaired.Duality
import blessed.SptCM.Interfaces

/-!
# The inert square-coefficient endpoint

This module keeps the characteristic-zero duality calculation and the
characteristic-`ℓ` theta-support argument attached to the same integral
Ahlgren--Kim grid.  Coefficient duality is first descended from `ℚ` to `ℤ`
and only then reduced modulo `ℓ`.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic SptCM.RolenLiterature

/-- Coefficient duality reduced from the rational realization of the one
integral published grid. -/
theorem mod_actual_coefficient_duality
    {Form Product : Type*} [SMul ℂ Form]
    (D : IntegralGridRealization)
    (E : EtaJGeneratorBasis Form)
    (R : WeightTwoMultiplicationTheory ℚ Form Product E D.rationalGrid)
    (ℓ k m : ℕ) [Fact ℓ.Prime]
    (hk : 0 < k) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (a : ℤ) :
    actualAuxiliarySeries (K := ZMod ℓ) E k a ((m : ℤ) ^ 2) =
      -D.modGrid ℓ m ((24 * k - 1 : ℕ) : ℤ) -
        (chi12 m : ZMod ℓ) * (a : ZMod ℓ) := by
  have hq := actual_coefficient_duality E D.rationalGrid R k m hk hm hm6 a
  rw [D.rational_grid] at hq
  change
    (auxiliaryHn E.toEtaJPowerBasis k a ((m : ℤ) ^ 2) : ℚ) =
      -(D.grid m ((24 * k - 1 : ℕ) : ℤ) : ℚ) -
        ((chi12 (m : ℤ) : ℤ) : ℚ) * (a : ℚ) at hq
  have hz :
      auxiliaryHn E.toEtaJPowerBasis k a ((m : ℤ) ^ 2) =
        -D.grid m ((24 * k - 1 : ℕ) : ℤ) - (chi12 m : ℤ) * a := by
    exact_mod_cast hq
  have hzmod := congrArg (fun z : ℤ => (z : ZMod ℓ)) hz
  simpa [actualAuxiliarySeries, IntegralGridRealization.modGrid,
    castIntegralSeries] using hzmod

/-- An index in the progression `23 mod 24` has the unique positive
parameterization used by the auxiliary form. -/
lemma exists_auxiliary_index_of_mod_eq_23
    {n : ℕ} (hn : n % 24 = 23) :
    ∃ k : ℕ, 0 < k ∧ n = 24 * k - 1 := by
  refine ⟨(n + 1) / 24, ?_, ?_⟩
  · omega
  · omega

/-- Admissibility is precisely the inertness assertion required by the theta
cycle at the signed discriminant `-n`. -/
lemma legendre_neg_eq_neg_one_of_admissible
    (ℓ n : ℕ) [Fact ℓ.Prime] (hadm : SptCM.Admissible ℓ n) :
    legendreSym ℓ (-(n : ℤ)) = -1 := by
  rw [legendreSym.eq_neg_one_iff]
  simpa using hadm.2.2

/-- The exact square-coefficient vanishing used in the paper.  The auxiliary
index `k` is obtained internally from admissibility; `m = 1` uses the
normalization coefficient, while `m > 1` uses reduced integral-grid duality
and I06 theta support. -/
theorem actual_square_coefficient_vanish
    {Form Product : Type*} [SMul ℂ Form]
    (D : IntegralGridRealization)
    (E : EtaJGeneratorBasis Form)
    (R : WeightTwoMultiplicationTheory ℚ Form Product E D.rationalGrid)
    (ℓ n m : ℕ) [Fact ℓ.Prime]
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hadm : SptCM.Admissible ℓ n)
    (hmAllowed : ValidGridIndex ℓ m)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ) :
    let k := (n + 1) / 24
    actualAuxiliarySeries (K := ZMod ℓ) E k (aCoeff (n : ℤ))
      ((m : ℤ) ^ 2) = 0 := by
  dsimp only
  obtain ⟨k, hk, hn⟩ := exists_auxiliary_index_of_mod_eq_23 hadm.2.1
  have hkdef : (n + 1) / 24 = k := by omega
  rw [hkdef]
  have hinert : legendreSym ℓ (-(n : ℤ)) = -1 :=
    legendre_neg_eq_neg_one_of_admissible ℓ n hadm
  have hn' : (24 * k - 1 : ℕ) = n := hn.symm
  by_cases hm1 : m = 1
  · subst m
    norm_num
    simpa [hn'] using
      (actual_Hn_first_coefficient_eq_zero_of_canonical_inert
        ℓ k E hk hcanonical hAK hEuler (by simpa [hn'] using hinert))
  · have hmpos : 1 < m := by
      have hm6 : Nat.Coprime m 6 :=
        Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hmAllowed
      have hm0 : m ≠ 0 := by
        intro h
        subst m
        simp at hm6
      omega
    have hm6 : Nat.Coprime m 6 :=
      Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hmAllowed
    have hf : HasPaperThetaCycle ℓ (fSeriesMod ℓ) :=
      theta_cycle_of_canonical_exact ℓ hcanonical hAK
    have hgridCycle : HasPaperThetaCycle ℓ (D.modGrid ℓ m) :=
      actual_modGrid_theta_support D ℓ m hcanonical.five_le hmAllowed hf
    have ha : (aCoeff (n : ℤ) : ZMod ℓ) = 0 :=
      aCoeff_mod_eq_zero_of_canonical_inert_exact ℓ (n : ℤ)
        hcanonical hAK hEuler hinert
    have hb : D.modGrid ℓ m (n : ℤ) = 0 :=
      gridCoeff_eq_zero_of_inert ℓ (D.modGrid ℓ m) (n : ℤ)
        hgridCycle hEuler hinert
    have hdual := mod_actual_coefficient_duality D E R ℓ k m hk hmpos hm6
      (aCoeff (n : ℤ))
    rw [hn', hb, ha] at hdual
    simpa using hdual

end SptCM.Analytic.Repaired
