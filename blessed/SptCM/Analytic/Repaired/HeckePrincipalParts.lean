import blessed.SptCM.Analytic.Repaired.Grid
import Mathlib.Tactic

/-!
# Exact principal-part calculations for the paper's Hecke identities

This module performs the coefficient calculation in I05.  It contains no
modularity, shadow, or uniqueness assumption: those analytic qualifications
remain separate.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic

/-- The mock form `f` has its only negative coefficient at index `-1`, with
coefficient one. -/
def HasMockPrincipalPart {K : Type*} [Ring K] (f : QSeries K) : Prop :=
  ∀ r : ℤ, r < 0 → f r = if r = -1 then 1 else 0

/-- The paper's actual integral coefficient series has exactly the asserted
mock-form negative principal part. -/
theorem fSeries_hasMockPrincipalPart :
    HasMockPrincipalPart fSeries := by
  intro r hr
  rw [fSeries, aCoeff]
  by_cases hr1 : r = -1
  · simp [hr1]
  · simp [hr1, show ¬(0 ≤ r ∧ r % 24 = 23) by omega]

/-- Casting the actual integral mock series into a characteristic-zero field
preserves its negative principal part. -/
theorem fSeries_cast_hasMockPrincipalPart
    {K : Type*} [Field K] [CharZero K] :
    HasMockPrincipalPart (fun r => (fSeries r : K)) := by
  intro r hr
  change (fSeries r : K) = _
  rw [fSeries_hasMockPrincipalPart r hr]
  by_cases hr1 : r = -1 <;> simp [hr1]

/-- The actual left side of the `f`-Hecke identity in the coefficient model. -/
def fHeckeDifference {K : Type*} [Field K]
    (p : ℕ) (chiP : K) (legendre : ℤ → K) (f : QSeries K) : QSeries K :=
  fun r => heckeThreeHalf p chiP legendre f r -
    chiP * (1 + (p : K)) * f r

/-- Mathlib's Legendre symbol, cast to the coefficient field used by the
Hecke coefficient formula. -/
def heckeLegendreCast {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    (r : ℤ) : K :=
  (legendreSym p r : ℤ)

@[simp] theorem heckeLegendreCast_one
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] :
    heckeLegendreCast (K := K) p 1 = 1 := by
  simp [heckeLegendreCast]

/-- The cast Legendre symbol has the exact prime-square value used in the
grid-Hecke principal-part computation. -/
theorem heckeLegendreCast_square
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (a : ℤ) :
    heckeLegendreCast (K := K) p (a ^ 2) =
      if (p : ℤ) ∣ a then 0 else 1 := by
  by_cases hpa : (p : ℤ) ∣ a
  · rw [if_pos hpa]
    have ha0 : (a : ZMod p) = 0 := by
      rw [CharP.intCast_eq_zero_iff]
      exact hpa
    have hs : legendreSym p (a ^ 2) = 0 := by
      apply (legendreSym.eq_zero_iff p (a ^ 2)).2
      simp [ha0]
    simp [heckeLegendreCast, hs]
  · rw [if_neg hpa]
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, CharP.intCast_eq_zero_iff]
      exact hpa
    have hs := legendreSym.sq_one' p ha0
    simp [heckeLegendreCast, hs]

/-- The negative Fourier coefficients of
`f | T(p²) - χ₁₂(p)(1+p)f` are exactly those of `p G_p`.

This is the explicit principal-part calculation used in I05.  The sole
quadratic-symbol input is `(1/p)=1`; no modular qualification or desired
Hecke identity is assumed. -/
theorem fHeckeDifference_hasGridPrincipalPart
    {K : Type*} [Field K]
    (p : ℕ) (hp : p.Prime) (chi : ℕ → K) (legendre : ℤ → K)
    (hp0 : (p : K) ≠ 0) (hlegendreOne : legendre 1 = 1) (f : QSeries K)
    (hf : HasMockPrincipalPart f) :
    HasGridPrincipalPart chi p
      (fun r => (p : K)⁻¹ * fHeckeDifference p (chi p) legendre f r) := by
  intro r hr
  have hp1 : 1 < p := hp.one_lt
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  by_cases hrp : r = -(p : ℤ) ^ 2
  · subst r
    have hnegp : (-(p : ℤ) ^ 2 : ℤ) < 0 := by nlinarith
    have hscale_ne : (p : ℤ) ^ 2 * (-(p : ℤ) ^ 2) ≠ -1 := by
      nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp1]
    have hbase_ne : (-(p : ℤ) ^ 2 : ℤ) ≠ -1 := by
      nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp1]
    have hscale := hf ((p : ℤ) ^ 2 * (-(p : ℤ) ^ 2)) (by nlinarith)
    rw [if_neg hscale_ne] at hscale
    have hbase := hf (-(p : ℤ) ^ 2) hnegp
    rw [if_neg hbase_ne] at hbase
    have hdiv : (p : ℤ) ^ 2 ∣ -(p : ℤ) ^ 2 := ⟨-1, by ring⟩
    have hquot : (-(p : ℤ) ^ 2) / (p : ℤ) ^ 2 = -1 := by
      rw [Int.neg_ediv]
      simp [hp.ne_zero]
    simp only [fHeckeDifference, heckeThreeHalf]
    rw [hscale, hbase, if_pos hdiv, hquot, hf (-1) (by omega)]
    simp [hp0]
  · by_cases hr1 : r = -1
    · subst r
      have hscale_ne : (p : ℤ) ^ 2 * (-1) ≠ -1 := by
        nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp1]
      have hscale := hf ((p : ℤ) ^ 2 * (-1)) (by nlinarith)
      rw [if_neg hscale_ne] at hscale
      have hnotdiv : ¬ (p : ℤ) ^ 2 ∣ (-1 : ℤ) := by
        intro h
        have habs := Int.natAbs_dvd_natAbs.mpr h
        norm_num at habs
        have : p ^ 2 = 1 := Nat.dvd_one.mp (by simpa using habs)
        nlinarith
      simp only [fHeckeDifference, heckeThreeHalf]
      rw [hscale, hf (-1) (by omega), if_neg hnotdiv]
      simp only [Int.neg_neg, hlegendreOne]
      have hpSqNe : (1 : ℤ) ≠ (p : ℤ) ^ 2 := by
        nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp1]
      simp [hpSqNe]
      field_simp
      ring
    · have hfr : f r = 0 := by simpa [hr1] using hf r hr
      have hscaledNeg : (p : ℤ) ^ 2 * r < 0 := by nlinarith [sq_nonneg (p : ℤ)]
      have hscaledNe : (p : ℤ) ^ 2 * r ≠ -1 := by
        intro h
        have hdiv : (p : ℤ) ∣ 1 := by
          use -(p : ℤ) * r
          nlinarith
        have habs := Int.natAbs_dvd_natAbs.mpr hdiv
        norm_num at habs
        have : p = 1 := Nat.dvd_one.mp (by simpa using habs)
        omega
      have hfscaled : f ((p : ℤ) ^ 2 * r) = 0 := by
        simpa [hscaledNe] using hf ((p : ℤ) ^ 2 * r) hscaledNeg
      by_cases hdiv : (p : ℤ) ^ 2 ∣ r
      · rcases hdiv with ⟨z, rfl⟩
        have hzneg : z < 0 := by
          have hp2pos : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
          nlinarith
        have hz_ne : z ≠ -1 := by
          intro hz
          subst z
          exact hrp (by ring)
        have hquot : ((p : ℤ) ^ 2 * z) / (p : ℤ) ^ 2 = z := by
          exact Int.mul_ediv_cancel_left z (by positivity)
        simp only [fHeckeDifference, heckeThreeHalf]
        rw [hfscaled, hfr, if_pos ⟨z, rfl⟩, hquot, hf z hzneg]
        simp only [if_neg hz_ne, mul_zero, add_zero, sub_zero]
        simp [hrp, hr1]
      · simp [fHeckeDifference, heckeThreeHalf, hfscaled, hfr, hdiv, hrp, hr1]

/-- The principal-part calculation specialized to the paper's actual
integral mock series after embedding it in a characteristic-zero field. -/
theorem actualFHeckeDifference_hasGridPrincipalPart
    {K : Type*} [Field K] [CharZero K]
    (p : ℕ) (hp : p.Prime) (chi : ℕ → K) (legendre : ℤ → K)
    (hlegendreOne : legendre 1 = 1) :
    HasGridPrincipalPart chi p
      (fun r => (p : K)⁻¹ *
        fHeckeDifference p (chi p) legendre (fun s => (fSeries s : K)) r) :=
  fHeckeDifference_hasGridPrincipalPart p hp chi legendre
    (Nat.cast_ne_zero.mpr hp.ne_zero) hlegendreOne _
    fSeries_cast_hasMockPrincipalPart

/-- Fully concrete `f`-side principal-part calculation using Mathlib's
Legendre symbol rather than a caller-supplied quadratic-symbol function. -/
theorem actualFHeckeDifference_legendre_hasGridPrincipalPart
    {K : Type*} [Field K] [CharZero K]
    (p : ℕ) [Fact p.Prime] (chi : ℕ → K) :
    HasGridPrincipalPart chi p
      (fun r => (p : K)⁻¹ *
        fHeckeDifference p (chi p) (heckeLegendreCast p)
          (fun s => (fSeries s : K)) r) :=
  actualFHeckeDifference_hasGridPrincipalPart p (Fact.out) chi
    (heckeLegendreCast p) (heckeLegendreCast_one p)

end SptCM.Analytic.Repaired
