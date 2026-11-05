module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

public section


/-!
# The four-component quadratic Gauss sum at level twelve

This file carries out the finite calculation used for the `S`-generator in
Rolen's Weil-representation argument.  It is deliberately independent of the
general Borcherds interface.
-/

namespace SptCM.Analytic.Repaired

/-- The four nonzero values of the primitive quadratic character modulo
twelve, written on the canonical representatives. -/
@[expose]
def chiTwelveResidue (s : Fin 12) : ℤ :=
  if s = 1 then 1
  else if s = 5 then -1
  else if s = 7 then -1
  else if s = 11 then 1
  else 0

/-- The inverse primitive twelfth root used by the Fourier transform
`e(-rs/12)`. -/
@[expose]
noncomputable def inverseTwelfthRoot : ℂ :=
  (Real.sqrt 3 / 2 : ℂ) - Complex.I / 2

/-- The level-twelve character Gauss sum.  The omitted eight summands have
zero character value, so this is literally the four nonzero terms of the
usual sum over `r mod 12`. -/
@[expose]
noncomputable def chiTwelveGaussSum (s : Fin 12) : ℂ :=
  inverseTwelfthRoot ^ s.val -
    inverseTwelfthRoot ^ ((5 * s.val) % 12) -
    inverseTwelfthRoot ^ ((7 * s.val) % 12) +
    inverseTwelfthRoot ^ ((11 * s.val) % 12)

private theorem sqrt_twelve : Real.sqrt 12 = 2 * Real.sqrt 3 := by
  have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have h12 : 0 ≤ Real.sqrt 12 := Real.sqrt_nonneg 12
  have hs12 : (Real.sqrt 12) ^ 2 = 12 := by norm_num
  nlinarith

set_option maxHeartbeats 800000 in
/-- The finite quadratic Gauss sum is `√12 χ₁₂(s)`.  The proof first
certifies the complete power table for the chosen inverse twelfth root and
then evaluates all twelve output components. -/
theorem chiTwelve_gauss_sum (s : Fin 12) :
    chiTwelveGaussSum s =
      (Real.sqrt 12 : ℂ) * (chiTwelveResidue s : ℂ) := by
  rw [sqrt_twelve]
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  let a : ℂ := (Real.sqrt 3 / 2 : ℂ)
  let z : ℂ := inverseTwelfthRoot
  have hz : z = a - Complex.I / 2 := by
    simp [z, a, inverseTwelfthRoot]
  have ha2 : a ^ 2 = (3 / 4 : ℂ) := by
    rw [pow_two]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z0 : z ^ 0 = 1 := by simp
  have z1 : z ^ 1 = a - Complex.I / 2 := by simpa [hz]
  have z2 : z ^ 2 = (1 / 2 : ℂ) - a * Complex.I := by
    rw [pow_succ, z1, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z3 : z ^ 3 = -Complex.I := by
    rw [pow_succ, z2, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z4 : z ^ 4 = (-1 / 2 : ℂ) - a * Complex.I := by
    rw [pow_succ, z3, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z5 : z ^ 5 = -a - Complex.I / 2 := by
    rw [pow_succ, z4, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z6 : z ^ 6 = -1 := by
    rw [pow_succ, z5, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z7 : z ^ 7 = -a + Complex.I / 2 := by
    rw [pow_succ, z6, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z8 : z ^ 8 = (-1 / 2 : ℂ) + a * Complex.I := by
    rw [pow_succ, z7, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z9 : z ^ 9 = Complex.I := by
    rw [pow_succ, z8, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z10 : z ^ 10 = (1 / 2 : ℂ) + a * Complex.I := by
    rw [pow_succ, z9, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  have z11 : z ^ 11 = a + Complex.I / 2 := by
    rw [pow_succ, z10, hz]
    apply Complex.ext <;> norm_num [a] <;> nlinarith [hs3]
  change z ^ s.val - z ^ ((5 * s.val) % 12) -
      z ^ ((7 * s.val) % 12) + z ^ ((11 * s.val) % 12) = _
  fin_cases s <;>
    simp [chiTwelveResidue, Fin.ext_iff, z0, z1, z2, z3, z4, z5,
      z6, z7, z8, z9, z10, z11, a] <;>
    ring

end SptCM.Analytic.Repaired
