import blessed.SptCM.Analytic.Repaired.Grid
import Mathlib.Tactic

/-!
# Principal parts in the grid Hecke recurrence

This module isolates the coefficient arithmetic needed for the second identity
in I05.  Nothing here assumes modular qualification or the desired Hecke
identity.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic

/-- The conventionally zero term `G_{m/p}` when `p ∤ m`.  When `m=p`, this is
`G₁`, so the published convention `G₁=0` gives the required cancellation. -/
def gridDivisorTerm {K : Type*} [Zero K]
    (G : ℕ → QSeries K) (m p : ℕ) : QSeries K :=
  if p ∣ m then G (m / p) else 0

/-- The source-normalized left side of Rolen's grid Hecke recurrence, solved
for `G_{mp}`. -/
def normalizedGridHeckeLeft {K : Type*} [Field K]
    (p m : ℕ) (chi : ℕ → K) (legendre : ℤ → K)
    (G : ℕ → QSeries K) : QSeries K :=
  fun r => (p : K)⁻¹ *
    (heckeThreeHalf p (chi p) legendre (G m) r
      - chi p * legendre ((m : ℤ) ^ 2) * G m r
      - gridDivisorTerm G m p r
      + (p : K) * chi m * G p r)

/-- On a negative exponent, a normalized grid member has exactly its two
published principal coefficients.  Unlike a bare principal-part statement,
this lemma also covers the exceptional index `a=1` using `G₁=0`. -/
theorem grid_negative_coefficient
    {K : Type*} [Field K] (chi : ℕ → K) (G : ℕ → QSeries K)
    (hG1 : G 1 = 0)
    (hGpp : ∀ a, 1 < a → HasGridPrincipalPart chi a (G a))
    (a : ℕ) (ha : 0 < a) (r : ℤ) (hr : r < 0) :
    G a r = if a = 1 then 0 else
      if r = -(a : ℤ) ^ 2 then 1 else if r = -1 then -chi a else 0 := by
  by_cases ha1 : a = 1
  · subst a
    simp [hG1]
  · rw [if_neg ha1]
    exact hGpp a (by omega) r hr

/-- Exact negative coefficients of the conventionally interpreted
`G_{m/p}` term.  In particular, the formula evaluates to zero when `m=p`,
because then the quotient index is one. -/
theorem gridDivisorTerm_negative_coefficient
    {K : Type*} [Field K] (chi : ℕ → K) (G : ℕ → QSeries K)
    (m p : ℕ) (hG1 : G 1 = 0)
    (hGdiv : p ∣ m → ∀ q, q = m / p → 1 < q → HasGridPrincipalPart chi q (G q))
    (hm : 0 < m) (hp : 0 < p) (r : ℤ) (hr : r < 0) :
    gridDivisorTerm G m p r =
      if h : p ∣ m then
        let q := m / p
        if q = 1 then 0 else
          if r = -(q : ℤ) ^ 2 then 1 else if r = -1 then -chi q else 0
      else 0 := by
  by_cases hpm : p ∣ m
  · simp only [gridDivisorTerm, hpm, if_true, Pi.zero_apply]
    have hqpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp
    by_cases hq1 : m / p = 1
    · rw [hq1, hG1]
      simp
    · rw [hGdiv hpm (m / p) rfl (by omega) r hr]
      simp [hq1]
  · simp [gridDivisorTerm, hpm]

/-- The convention `G₁=0` is exactly what removes the divisor term in the
collision case `m=p`. -/
theorem gridDivisorTerm_self_eq_zero
    {K : Type*} [Field K] (G : ℕ → QSeries K)
    (hG1 : G 1 = 0) (p : ℕ) (hp : 0 < p) :
    gridDivisorTerm G p p = 0 := by
  rw [gridDivisorTerm, if_pos (dvd_refl p), Nat.div_self hp, hG1]

/-- The normalized right side is the actual published grid member `G_{mp}`;
its principal part follows directly in the valid range. -/
theorem normalizedGridHeckeRight_hasGridPrincipalPart
    {K : Type*} [Field K] (chi : ℕ → K) (G : ℕ → QSeries K)
    (hGpp : ∀ a, 1 < a → HasGridPrincipalPart chi a (G a))
    (m p : ℕ) (hmp : 1 < m * p) :
    HasGridPrincipalPart chi (m * p) (G (m * p)) :=
  hGpp (m * p) hmp


/-- The divided-index summand of the weight `3/2` Hecke operator has exactly
the two expected negative coefficients.  This is the part of the recurrence
calculation that produces `p G_{mp}` and `-p χ(m) q^{-p²/24}`. -/
theorem dividedGridTerm_negative_coefficient
    {K : Type*} [Field K] (chi : ℕ → K) (G : ℕ → QSeries K)
    (m p : ℕ) (hGm : HasGridPrincipalPart chi m (G m))
    (hm : 1 < m) (hp : 0 < p) (r : ℤ) (hr : r < 0) :
    (if (p : ℤ) ^ 2 ∣ r then
        (p : K) * G m (r / (p : ℤ) ^ 2) else 0) =
      if r = -((m * p : ℕ) : ℤ) ^ 2 then (p : K)
      else if r = -(p : ℤ) ^ 2 then -(p : K) * chi m else 0 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  by_cases hdiv : (p : ℤ) ^ 2 ∣ r
  · rcases hdiv with ⟨z, rfl⟩
    have hzneg : z < 0 := by nlinarith [sq_pos_of_pos hpz]
    have hquot : ((p : ℤ) ^ 2 * z) / (p : ℤ) ^ 2 = z :=
      Int.mul_ediv_cancel_left z (by positivity)
    rw [if_pos ⟨z, rfl⟩, hquot,
      hGm z hzneg]
    have hlead : ((p : ℤ) ^ 2 * z = -((m * p : ℕ) : ℤ) ^ 2) ↔
        z = -(m : ℤ) ^ 2 := by
      push_cast
      constructor <;> intro h
      · nlinarith [sq_pos_of_pos hpz]
      · subst z
        ring
    have hpole : ((p : ℤ) ^ 2 * z = -(p : ℤ) ^ 2) ↔ z = -1 := by
      constructor <;> intro h
      · nlinarith [sq_pos_of_pos hpz]
      · subst z
        ring
    by_cases hzlead : z = -(m : ℤ) ^ 2
    · rw [if_pos hzlead, if_pos (hlead.mpr hzlead)]
      simp
    · rw [if_neg hzlead, if_neg (fun h => hzlead (hlead.mp h))]
      by_cases hzone : z = -1
      · rw [if_pos hzone, if_pos (hpole.mpr hzone)]
        ring
      · rw [if_neg hzone, if_neg (fun h => hzone (hpole.mp h))]
        simp
  · rw [if_neg hdiv]
    have hnelead : r ≠ -((m * p : ℕ) : ℤ) ^ 2 := by
      intro h
      apply hdiv
      use -((m : ℤ) ^ 2)
      push_cast at h ⊢
      nlinarith
    have hnepole : r ≠ -(p : ℤ) ^ 2 := by
      intro h
      apply hdiv
      exact ⟨-1, by nlinarith⟩
    have hnelead' : r ≠ -((m : ℤ) * p) ^ 2 := by
      simpa [Nat.cast_mul] using hnelead
    simp [hnelead, hnelead', hnepole, Nat.cast_mul]


/-- The scaled-index summand of the Hecke operator moves the leading pole
from `m` to `m/p` exactly when `p ∣ m`; its `q⁻¹` coefficient can never
contribute at a negative integral index after scaling by `p²`. -/
theorem scaledGridTerm_negative_coefficient
    {K : Type*} [Field K] (chi : ℕ → K) (G : ℕ → QSeries K)
    (m p : ℕ) (hGm : HasGridPrincipalPart chi m (G m))
    (hm : 1 < m) (hp : p.Prime) (r : ℤ) (hr : r < 0) :
    G m ((p : ℤ) ^ 2 * r) =
      if h : p ∣ m then
        if r = -((m / p : ℕ) : ℤ) ^ 2 then 1 else 0
      else 0 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hneg : (p : ℤ) ^ 2 * r < 0 := by nlinarith [sq_pos_of_pos hpz]
  rw [hGm _ hneg]
  have hneone : (p : ℤ) ^ 2 * r ≠ -1 := by
    intro h
    have hd : (p : ℤ) ∣ 1 := by
      use -(p : ℤ) * r
      nlinarith
    have : p ∣ 1 := by exact_mod_cast hd
    exact hp.not_dvd_one this
  rw [if_neg hneone]
  by_cases hpm : p ∣ m
  · obtain ⟨q, rfl⟩ := hpm
    have hqpos : 0 < q := by
      by_contra hq
      have : q = 0 := by omega
      subst q
      simp at hm
    have hquot : p * q / p = q := by
      simpa [Nat.mul_comm] using Nat.mul_div_left q hp.pos
    rw [dif_pos (dvd_mul_right p q), hquot]
    have heq : ((p : ℤ) ^ 2 * r = -((p * q : ℕ) : ℤ) ^ 2) ↔
        r = -(q : ℤ) ^ 2 := by
      push_cast
      constructor <;> intro h
      · nlinarith [sq_pos_of_pos hpz]
      · subst r
        ring
    by_cases hrq : r = -(q : ℤ) ^ 2
    · rw [if_pos (heq.mpr hrq), if_pos hrq]
    · rw [if_neg (fun h => hrq (heq.mp h)), if_neg hrq]
  · rw [dif_neg hpm]
    have hne : (p : ℤ) ^ 2 * r ≠ -(m : ℤ) ^ 2 := by
      intro h
      have hdint : (p : ℤ) ∣ (m : ℤ) ^ 2 := by
        use -(p : ℤ) * r
        nlinarith
      have hd : p ∣ m ^ 2 := by exact_mod_cast hdint
      exact hpm (hp.dvd_of_dvd_pow hd)
    rw [if_neg hne]

end SptCM.Analytic.Repaired

namespace SptCM.Analytic.Repaired

open SptCM.Analytic

/-- The source-normalized left side of the grid Hecke recurrence has the
published principal part.  All modular qualification is deliberately absent:
this is only the internal Fourier-coefficient calculation. -/
theorem normalizedGridHeckeLeft_hasGridPrincipalPart
    {K : Type*} [Field K]
    (chi : ℕ → K) (legendre : ℤ → K) (G : ℕ → QSeries K)
    (hchiOne : chi 1 = 1)
    (hchiMul : ∀ a b, chi (a * b) = chi a * chi b)
    (m p : ℕ)
    (hG1 : G 1 = 0)
    (hGm : HasGridPrincipalPart chi m (G m))
    (hGp : HasGridPrincipalPart chi p (G p))
    (hGdiv : p ∣ m → ∀ q, q = m / p → 1 < q → HasGridPrincipalPart chi q (G q))
    (hm : 1 < m) (hp : p.Prime)
    (hp0 : (p : K) ≠ 0)
    (hchiPSq : chi p * chi p = 1)
    (hlegendreOne : legendre 1 = 1)
    (hlegendreSquares : ∀ a : ℤ, legendre (a ^ 2) =
      if (p : ℤ) ∣ a then 0 else 1) :
    HasGridPrincipalPart chi (m * p)
      (normalizedGridHeckeLeft p m chi legendre G) := by
  intro r hr
  let δ : ℤ → K := fun e => if r = e then 1 else 0
  have hpair (a : ℕ) (ha : 1 < a) :
      (if r = -(a : ℤ) ^ 2 then (1 : K)
       else if r = -1 then -chi a else 0) =
        δ (-(a : ℤ) ^ 2) + (-chi a) * δ (-1) := by
    have hne : (-(a : ℤ) ^ 2 : ℤ) ≠ -1 := by
      intro h
      have haZ : (2 : ℤ) ≤ a := by exact_mod_cast ha
      nlinarith
    by_cases h₁ : r = -(a : ℤ) ^ 2
    · have h₂ : r ≠ -1 := fun h => hne (h₁.symm.trans h)
      simp only [if_pos h₁, δ, if_neg h₂, mul_zero, add_zero]
    · simp only [if_neg h₁, δ]
      split_ifs <;> ring
  have hGmCoeff : G m r =
      δ (-(m : ℤ) ^ 2) + (-chi m) * δ (-1) := by
    rw [hGm r hr]
    exact hpair m hm
  have hGpCoeff : G p r =
      δ (-(p : ℤ) ^ 2) + (-chi p) * δ (-1) := by
    rw [hGp r hr]
    exact hpair p hp.one_lt
  have hscaled := scaledGridTerm_negative_coefficient chi G m p hGm
    hm hp r hr
  have hdivided := dividedGridTerm_negative_coefficient chi G m p hGm
    hm hp.pos r hr
  have hdivisor := gridDivisorTerm_negative_coefficient chi G m p hG1 hGdiv
    (by omega) hp.pos r hr
  have hleggrid :
      chi p * legendre (-r) * G m r =
        (chi p * legendre ((m : ℤ) ^ 2)) * δ (-(m : ℤ) ^ 2) +
        (-chi p * legendre 1 * chi m) * δ (-1) := by
    rw [hGmCoeff]
    simp only [mul_add]
    congr 1
    · simp only [δ]
      split_ifs with h <;> subst_vars <;> simp
    · simp only [δ]
      split_ifs with h <;> subst_vars <;> simp <;> ring
  have hfixedgrid :
      chi p * legendre ((m : ℤ) ^ 2) * G m r =
        (chi p * legendre ((m : ℤ) ^ 2)) * δ (-(m : ℤ) ^ 2) +
        (-chi p * legendre ((m : ℤ) ^ 2) * chi m) * δ (-1) := by
    rw [hGmCoeff]
    ring
  have hGpScaled :
      (p : K) * chi m * G p r =
        ((p : K) * chi m) * δ (-(p : ℤ) ^ 2) +
        (-(p : K) * chi m * chi p) * δ (-1) := by
    rw [hGpCoeff]
    ring
  have hdivided' :
      (if (p : ℤ) ^ 2 ∣ r then
          (p : K) * G m (r / (p : ℤ) ^ 2) else 0) =
        (p : K) * δ (-((m * p : ℕ) : ℤ) ^ 2) +
        (-(p : K) * chi m) * δ (-(p : ℤ) ^ 2) := by
    rw [hdivided]
    have hne : (-((m * p : ℕ) : ℤ) ^ 2 : ℤ) ≠ -(p : ℤ) ^ 2 := by
      intro h
      have h' : ((m : ℤ) * (p : ℤ)) ^ 2 = (p : ℤ) ^ 2 := by
        exact neg_inj.mp (by simpa [Nat.cast_mul] using h)
      rw [mul_pow] at h'
      have hp2ne : (p : ℤ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
      have hm2 : (m : ℤ) ^ 2 = 1 := by
        apply mul_right_cancel₀ hp2ne
        simpa using h'
      have hmZ : (2 : ℤ) ≤ m := by exact_mod_cast hm
      nlinarith
    by_cases h₁ : r = -((m * p : ℕ) : ℤ) ^ 2
    · have h₂ : r ≠ -(p : ℤ) ^ 2 := fun h => hne (h₁.symm.trans h)
      simp only [if_pos h₁, δ, if_neg h₂, mul_one, mul_zero, add_zero]
    · simp only [if_neg h₁, δ, zero_add]
      split_ifs <;> ring
  have htarget :
      (if r = -((m * p : ℕ) : ℤ) ^ 2 then (1 : K)
       else if r = -1 then -chi (m * p) else 0) =
        δ (-((m * p : ℕ) : ℤ) ^ 2) +
          (-chi (m * p)) * δ (-1) := by
    exact hpair (m * p) (by exact Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m hp.pos))
  simp only [normalizedGridHeckeLeft, heckeThreeHalf]
  rw [hscaled, hleggrid, hdivided', hfixedgrid, hdivisor, hGpScaled,
    htarget]
  rw [hlegendreSquares, hlegendreOne]
  by_cases hpm : p ∣ m
  · obtain ⟨q, rfl⟩ := hpm
    have hqpos : 0 < q := by
      by_contra hq
      have : q = 0 := by omega
      subst q
      simp at hm
    have hquot : p * q / p = q := by
      simpa [Nat.mul_comm] using Nat.mul_div_left q hp.pos
    have hpdvd : (p : ℤ) ∣ (p * q : ℕ) := by
      exact_mod_cast dvd_mul_right p q
    simp only [hpdvd, if_true, dvd_mul_right, dite_true, hquot]
    have hchiM : chi (p * q) = chi p * chi q := hchiMul p q
    have hchiTarget : chi ((p * q) * p) = chi q := by
      rw [hchiMul, hchiM]
      calc
        chi p * chi q * chi p = (chi p * chi p) * chi q := by ring
        _ = chi q := by rw [hchiPSq, one_mul]
    rw [hchiM, hchiTarget]
    by_cases hq1 : q = 1
    · subst q
      simp only [hchiOne, mul_one]
      simp only [δ]
      field_simp [hp0]
      ring_nf at hchiPSq ⊢
      rw [hchiPSq]
      simp only [if_true]
      ring
    · have hqgt : 1 < q := by omega
      rw [if_neg hq1, hpair q hqgt]
      simp only [δ]
      field_simp [hp0]
      ring_nf at hchiPSq ⊢
      rw [hchiPSq]
      ring
  · have hpnotdvd : ¬(p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpm
    simp only [hpnotdvd, if_false, hpm, dite_false]
    rw [hchiMul]
    simp only [δ]
    field_simp [hp0]
    ring

end SptCM.Analytic.Repaired
