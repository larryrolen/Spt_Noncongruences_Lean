import blessed.SptCM.CM.Repaired.HauptmodulCoordinate
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# The analytic Euler product for the level-six Hauptmodul

This file connects the actual Dedekind eta function in Mathlib to the Euler
product whose formal expansion begins `q⁻¹ - 5 + O(q)`.  Extracting that
analytic product as a formal Laurent series is kept as a separate remaining
step.
-/

namespace SptCM.Repair

open scoped ModularForm

/-- The unit Euler product occurring in Mathlib's definition of Dedekind eta. -/
noncomputable def etaEulerUnit (z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - ModularForm.eta_q n z)

/-- The level-six Euler-product quotient after removing the net `q⁻¹`
prefactor from the eta quotient. -/
noncomputable def hauptmodulEulerUnit (τ : UpperHalfPlane) : ℂ :=
  etaEulerUnit τ ^ 5 * etaEulerUnit (3 * (τ : ℂ)) /
    (etaEulerUnit (2 * (τ : ℂ)) * etaEulerUnit (6 * (τ : ℂ)) ^ 5)

/-- Mathlib's actual Dedekind eta quotient is exactly `q⁻¹` times its unit
Euler product.  This is the analytic bridge; no Laurent principal part is
assumed. -/
theorem analyticHauptmodul_eq_qParam_inv_mul_eulerUnit
    (τ : UpperHalfPlane) :
    SptCM.CM.Repaired.analyticHauptmodul τ =
      (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ * hauptmodulEulerUnit τ := by
  unfold SptCM.CM.Repaired.analyticHauptmodul SptCM.hauptmodul
    ModularForm.eta hauptmodulEulerUnit etaEulerUnit
  rw [show Function.Periodic.qParam 24 (3 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 3 by
        simp [Function.Periodic.qParam, ← Complex.exp_nsmul]
        ring_nf,
    show Function.Periodic.qParam 24 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 2 by
        simp [Function.Periodic.qParam, ← Complex.exp_nsmul]
        ring_nf,
    show Function.Periodic.qParam 24 (6 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 6 by
        simp [Function.Periodic.qParam, ← Complex.exp_nsmul]
        ring_nf,
    show Function.Periodic.qParam 1 (τ : ℂ) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 24 by
        simp [Function.Periodic.qParam, ← Complex.exp_nsmul]
        ring_nf]
  have hq : Function.Periodic.qParam 24 (τ : ℂ) ≠ 0 := by
    simp [Function.Periodic.qParam]
  field_simp

end SptCM.Repair
