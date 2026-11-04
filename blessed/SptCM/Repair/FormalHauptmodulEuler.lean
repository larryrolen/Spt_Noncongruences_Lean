module

public import blessed.SptCM.Analytic.Repaired.EulerProducts
public import blessed.SptCM.Repair.LaurentHauptmodul
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PowerSeries.Substitution

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Formal Euler product of the level-six Hauptmodul

This constructs the formal unit Euler product independently of the analytic
Dedekind eta quotient.  Analytic/formal identification is deliberately not
asserted here.
-/

namespace SptCM.Repair

open scoped PowerSeries

/-- The contribution of the `m`-th Euler index to the unit part of
`η(τ)^5 η(3τ) / (η(2τ) η(6τ)^5)`. -/
@[expose]
noncomputable def hauptmodulFormalEulerFactor (m : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ m) ^ 5 * (1 - PowerSeries.X ^ (3 * m)) *
    PowerSeries.subst (PowerSeries.X ^ (2 * m))
      (PowerSeries.invOneSubPow ℤ 1 : PowerSeries ℤ) *
    PowerSeries.subst (PowerSeries.X ^ (6 * m))
      (PowerSeries.invOneSubPow ℤ 5 : PowerSeries ℤ)

/-- The coefficientwise stabilized formal Euler product for the level-six
Hauptmodul's unit part.  Degree `d` is read from the first `d+2` positive
Euler indices, after which no omitted factor can affect it. -/
@[expose]
noncomputable def hauptmodulFormalEulerUnit : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    PowerSeries.coeff d
      (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1))

private theorem coeff_hauptmodulFormalEulerUnit (d : ℕ) :
    PowerSeries.coeff d hauptmodulFormalEulerUnit =
      PowerSeries.coeff d
        (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1)) := by
  simp [hauptmodulFormalEulerUnit]

/-- The formal unit Euler product is normalized. -/
theorem hauptmodulFormalEulerUnit_coeff_zero :
    PowerSeries.coeff 0 hauptmodulFormalEulerUnit = 1 := by
  rw [coeff_hauptmodulFormalEulerUnit]
  norm_num [hauptmodulFormalEulerFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    PowerSeries.invOneSubPow, Finset.prod_range_succ]

/-- The formal unit part is genuinely a unit of `ℤ[[q]]`, not merely a
series to which the word “unit” has been attached. -/
theorem hauptmodulFormalEulerUnit_isUnit :
    IsUnit hauptmodulFormalEulerUnit := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    hauptmodulFormalEulerUnit_coeff_zero]
  exact isUnit_one

/-- Its linear coefficient is `-5`; only `(1-X)^5` from the first Euler
index contributes in degree one. -/
theorem hauptmodulFormalEulerUnit_coeff_one :
    PowerSeries.coeff 1 hauptmodulFormalEulerUnit = -5 := by
  rw [coeff_hauptmodulFormalEulerUnit]
  norm_num [hauptmodulFormalEulerFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    PowerSeries.invOneSubPow, Finset.prod_range_succ]

/-- The formal Laurent series obtained by adjoining the net `q⁻¹` prefactor
to the formal Euler unit.  This is not asserted to be the analytic eta
quotient's Laurent expansion. -/
@[expose]
noncomputable def hauptmodulFormalLaurent : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * (hauptmodulFormalEulerUnit : LaurentSeries ℤ)

/-- I15's formal integral unit expansion: the constructed Laurent series is
literally `q⁻¹` times an integral power-series unit of constant term one. -/
theorem hauptmodulFormalLaurent_integralUnitExpansion :
    hauptmodulFormalLaurent =
        HahnSeries.single (-1) 1 *
          (hauptmodulFormalEulerUnit : LaurentSeries ℤ) ∧
      PowerSeries.coeff 0 hauptmodulFormalEulerUnit = 1 ∧
      IsUnit hauptmodulFormalEulerUnit := by
  exact ⟨rfl, hauptmodulFormalEulerUnit_coeff_zero,
    hauptmodulFormalEulerUnit_isUnit⟩

/-- The independently constructed formal Euler product has the desired
principal part. -/
theorem hauptmodulFormalLaurent_principalPart :
    HasHauptmodulPrincipalPart hauptmodulFormalLaurent := by
  refine ⟨?_, ?_, ?_⟩
  · change
      (HahnSeries.single (-1) 1 *
        (hauptmodulFormalEulerUnit : LaurentSeries ℤ)).coeff
          ((0 : ℤ) + (-1)) = 1
    rw [HahnSeries.coeff_single_mul_add]
    simpa [PowerSeries.coeff_coe] using
      hauptmodulFormalEulerUnit_coeff_zero
  · change
      (HahnSeries.single (-1) 1 *
        (hauptmodulFormalEulerUnit : LaurentSeries ℤ)).coeff
          ((1 : ℤ) + (-1)) = -5
    rw [HahnSeries.coeff_single_mul_add]
    simpa [PowerSeries.coeff_coe] using
      hauptmodulFormalEulerUnit_coeff_one
  · intro z hz
    have hz' : z + 1 < 0 := by omega
    unfold hauptmodulFormalLaurent
    rw [← show (z + 1) + (-1) = z by omega]
    rw [HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    simp [hz']

end SptCM.Repair
