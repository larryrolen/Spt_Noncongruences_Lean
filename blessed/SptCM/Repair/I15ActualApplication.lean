import blessed.SptCM.Repair.AnalyticFormalIdentification

/-!
# The actual expansion input in the I15 application

This file feeds the analytic/formal coefficient identification into the
abstract E7 integral-curve argument.  The only remaining hypotheses are the
geometric comparison laws which interpret analytic nonvanishing and a
concrete integral `q`-expansion in the predicates of a chosen model.
-/

namespace SptCM.Repair

open scoped ModularForm PowerSeries

/-- A concrete integral unit expansion of an analytic function at infinity.
The power series is integral, is a unit with constant coefficient one, and
its complex evaluation on every upper-half-plane nome gives the analytic
function after adjoining the simple pole `q⁻¹`. -/
def HasActualIntegralUnitExpansion
    (f : UpperHalfPlane → ℂ) (u : PowerSeries ℤ) : Prop :=
  (∀ τ : UpperHalfPlane,
      f τ =
        (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ *
          (∑' n : ℕ,
            ((PowerSeries.coeff n u : ℤ) : ℂ) *
              Function.Periodic.qParam 1 (τ : ℂ) ^ n)) ∧
    PowerSeries.coeff 0 u = 1 ∧ IsUnit u

/-- The actual Mathlib eta quotient has the integral unit expansion given by
the independently constructed stabilized Euler product. -/
theorem analyticHauptmodul_hasActualIntegralUnitExpansion :
    HasActualIntegralUnitExpansion
      SptCM.CM.Repaired.analyticHauptmodul
      hauptmodulFormalEulerUnit := by
  refine ⟨analyticHauptmodul_eq_integral_formal_expansion, ?_⟩
  exact ⟨hauptmodulFormalEulerUnit_coeff_zero,
    hauptmodulFormalEulerUnit_isUnit⟩

/-- The E7 coordinate chain specialized to the actual analytic eta quotient
and its proved integral Euler expansion.  The two compatibility hypotheses
are interpretation laws for a chosen geometric model; neither assumes the
desired divisor, absence of vertical components, or coordinate conclusion. -/
theorem analyticHauptmodul_integral_coordinate_of_E7
    {Cusp Curve Divisor : Type*}
    (M : SptCM.RolenLiterature.LigozatModel
      SptCM.CM.Repaired.LevelSixEtaExponents
      (UpperHalfPlane → ℂ) Cusp ℚ Curve)
    (G : SptCM.RolenLiterature.IntegralCurveFunctionGeometry
      (UpperHalfPlane → ℂ) Divisor Curve Cusp (PowerSeries ℤ))
    (hLigozat : SptCM.RolenLiterature.LigozatEtaQuotients M)
    (hIntegral : SptCM.RolenLiterature.X0SixGoodIntegralModel M)
    (hGenusZero : SptCM.RolenLiterature.X0SixGenusZeroFibers M)
    (hCusps : SptCM.RolenLiterature.X0SixDisjointCusps M)
    (hHorizontal : SptCM.RolenLiterature.E7HorizontalDivisorPrinciple G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.isModularFunction M.cuspOrder)
    (hNoVertical : SptCM.RolenLiterature.E7NoVerticalComponentPrinciple G
      M.isIntegralModelAwayFromLevel M.hasDisjointStandardCuspSections)
    (hDegreeOne : SptCM.RolenLiterature.E7IntegralDegreeOneCriterion G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.hasDisjointStandardCuspSections)
    (X : Curve) (zero oneHalf oneThird infinity : Cusp)
    (hconditions :
      M.ligozatConditions SptCM.CM.Repaired.hauptmodulExponents)
    (hlevel : M.isLevelSixModularCurve X)
    (horders :
      M.orderFormula SptCM.CM.Repaired.hauptmodulExponents zero =
          SptCM.CM.Repaired.ligozatCuspOrder
            SptCM.CM.Repaired.hauptmodulExponents 1 ∧
      M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneHalf =
          SptCM.CM.Repaired.ligozatCuspOrder
            SptCM.CM.Repaired.hauptmodulExponents 2 ∧
      M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneThird =
          SptCM.CM.Repaired.ligozatCuspOrder
            SptCM.CM.Repaired.hauptmodulExponents 3 ∧
      M.orderFormula SptCM.CM.Repaired.hauptmodulExponents infinity =
          SptCM.CM.Repaired.ligozatCuspOrder
            SptCM.CM.Repaired.hauptmodulExponents 6)
    (hcuspCases : ∀ c : Cusp,
      c = zero ∨ c = oneHalf ∨ c = oneThird ∨ c = infinity)
    (hquotient :
      M.quotient SptCM.CM.Repaired.hauptmodulExponents =
        SptCM.CM.Repaired.analyticHauptmodul)
    (hNoInteriorCompatibility :
      ∀ f : UpperHalfPlane → ℂ, (∀ τ, f τ ≠ 0) →
        G.hasNoInteriorZeroOrPole f X)
    (hExpansionCompatibility :
      ∀ (f : UpperHalfPlane → ℂ) (u : PowerSeries ℤ),
        HasActualIntegralUnitExpansion f u →
          G.hasIntegralUnitExpansionAt f infinity u) :
    G.identifiesWithProjectiveLine
      (M.quotient SptCM.CM.Repaired.hauptmodulExponents) X := by
  have hinterior :
      G.hasNoInteriorZeroOrPole
        (M.quotient SptCM.CM.Repaired.hauptmodulExponents) X := by
    rw [hquotient]
    exact hNoInteriorCompatibility _
      SptCM.CM.Repaired.analyticHauptmodul_ne_zero
  have hexpansion :
      G.hasIntegralUnitExpansionAt
        (M.quotient SptCM.CM.Repaired.hauptmodulExponents) infinity
        hauptmodulFormalEulerUnit := by
    rw [hquotient]
    exact hExpansionCompatibility _ _
      analyticHauptmodul_hasActualIntegralUnitExpansion
  exact SptCM.CM.Repaired.hauptmodul_integral_coordinate_of_E7 M G
    hLigozat hIntegral hGenusZero hCusps hHorizontal hNoVertical hDegreeOne
    X zero oneHalf oneThird infinity hauptmodulFormalEulerUnit hconditions
    hlevel hinterior horders hcuspCases hexpansion

end SptCM.Repair
