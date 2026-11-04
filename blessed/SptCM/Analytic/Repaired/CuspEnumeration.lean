module

public import blessed.SptCM.Literature.SquarefreeCusps
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Tactic

public section


namespace SptCM.Analytic.Repaired

open CongruenceSubgroup

open SptCM.RolenLiterature

/-- The positive divisors of six are exactly `1, 2, 3, 6`. -/
theorem divisor_of_six_cases (d : ℕ) (hd : d ∣ 6) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
  have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> simp_all

/-- I11 cusp exhaustion.  The general squarefree-level classification and the
explicit divisor computation show that every cusp class on `X₀(6)` is one of
`0`, `1/2`, `1/3`, or `∞`, in exactly the divisor convention used for the
Atkin--Lehner/Weyl-vector formula. -/
theorem levelSix_cusp_exhaustion
    (hclassification : SquarefreeGammaZeroCuspClassification) :
    ∀ c : GammaZeroCusp 6,
      c = Quotient.mk'' ((0 : ℚ) : OnePoint ℚ) ∨
      c = Quotient.mk'' ((1 / 2 : ℚ) : OnePoint ℚ) ∨
      c = Quotient.mk'' ((1 / 3 : ℚ) : OnePoint ℚ) ∨
      c = Quotient.mk'' (OnePoint.infty : OnePoint ℚ) := by
  intro c
  have hsquarefree : Squarefree (6 : ℕ) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  obtain ⟨d, rfl⟩ :=
    (hclassification 6 (by norm_num) hsquarefree).2 c
  rcases divisor_of_six_cases d.1 d.2 with h | h | h | h
  · left
    simp [squarefreeCuspRepresentative, squarefreeCuspPoint, h]
  · right; left
    simp [squarefreeCuspRepresentative, squarefreeCuspPoint, h]
  · right; right; left
    simp [squarefreeCuspRepresentative, squarefreeCuspPoint, h]
  · right; right; right
    simp [squarefreeCuspRepresentative, squarefreeCuspPoint, h]

end SptCM.Analytic.Repaired
