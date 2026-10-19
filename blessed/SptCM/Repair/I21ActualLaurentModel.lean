import blessed.SptCM.Repair.AnalyticFormalIdentification
import blessed.SptCM.Repair.LaurentHauptmodul

/-!
# The actual integral Laurent model in finite characteristic

The series in this file is not selected merely by prescribing its principal
part.  It is the coefficientwise reduction of the independently constructed
integral Euler product `hauptmodulFormalLaurent`.
-/

namespace SptCM.Repair

/-- Coefficientwise reduction of the integral Euler-product Laurent series. -/
noncomputable def actualHauptmodulLaurent (ℓ : ℕ) : LaurentSeries (ZMod ℓ) :=
  HahnSeries.map hauptmodulFormalLaurent (Int.castRingHom (ZMod ℓ))

/-- Reduction commutes with every Laurent coefficient. -/
theorem actualHauptmodulLaurent_coeff (ℓ : ℕ) (z : ℤ) :
    (actualHauptmodulLaurent ℓ).coeff z =
      (hauptmodulFormalLaurent.coeff z : ZMod ℓ) := by
  simp [actualHauptmodulLaurent, HahnSeries.map_coeff]

/-- The reduced actual Euler model retains the integral principal part. -/
theorem actualHauptmodulLaurent_principalPart
    {ℓ : ℕ} [NeZero ℓ] :
    HasHauptmodulPrincipalPart (actualHauptmodulLaurent ℓ) := by
  rcases hauptmodulFormalLaurent_principalPart with ⟨hneg, hzero, hbelow⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [actualHauptmodulLaurent_coeff] using congrArg (fun x : ℤ => (x : ZMod ℓ)) hneg
  · simpa [actualHauptmodulLaurent_coeff] using congrArg (fun x : ℤ => (x : ZMod ℓ)) hzero
  · intro z hz
    rw [actualHauptmodulLaurent_coeff, hbelow z hz]
    simp

/-- The concrete Laurent datum supplied by coefficientwise reduction of the
integral Euler product. -/
noncomputable def actualLaurentHauptmodulData
    (ℓ n : ℕ) (hrange : AnalyticAdmissible ℓ n) :
    LaurentHauptmodulData ℓ n hrange where
  t := actualHauptmodulLaurent ℓ
  principalPart := by
    have : NeZero ℓ := ⟨hrange.prime.ne_zero⟩
    exact actualHauptmodulLaurent_principalPart

/-- The series field of the concrete datum is definitionally the reduction of
`hauptmodulFormalLaurent`; hence this is an actual model, rather than an
existential series chosen from its principal part. -/
theorem actualLaurentHauptmodulData_series
    (ℓ n : ℕ) (hrange : AnalyticAdmissible ℓ n) :
    (actualLaurentHauptmodulData ℓ n hrange).t = actualHauptmodulLaurent ℓ :=
  rfl


/-- The concrete reduced Laurent model is the coefficientwise reduction of
exactly the integral Laurent expansion of Mathlib's actual analytic eta
quotient, rather than merely a series with the same principal part. -/
theorem actualHauptmodulLaurent_analytic_identification
    (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) :
    SptCM.CM.Repaired.analyticHauptmodul τ =
        (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ *
          (∑' n : ℕ,
            ((PowerSeries.coeff n hauptmodulFormalEulerUnit : ℤ) : ℂ) *
              Function.Periodic.qParam 1 (τ : ℂ) ^ n) ∧
      (∀ z : ℤ, (actualHauptmodulLaurent ℓ).coeff z =
        (hauptmodulFormalLaurent.coeff z : ZMod ℓ)) ∧
      HasHauptmodulPrincipalPart (actualHauptmodulLaurent ℓ) := by
  exact ⟨analyticHauptmodul_eq_integral_formal_expansion τ,
    actualHauptmodulLaurent_coeff ℓ,
    actualHauptmodulLaurent_principalPart⟩

end SptCM.Repair
