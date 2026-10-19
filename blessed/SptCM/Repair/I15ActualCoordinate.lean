import blessed.SptCM.Repair.I15ActualApplication

/-!
# The standard `X₀(6)` application of the integral-coordinate argument

This module gives a single, source-facing boundary for the standard integral
model of `X₀(6)`.  Its fields are only comparison and interpretation facts:
the standard cusp labels, the identification of the Ligozat quotient with
the actual eta quotient, and the general integral-curve principles.  It does
not contain a divisor, a no-vertical-component conclusion, or a coordinate
conclusion.  Those are derived below.
-/

namespace SptCM.Repair

open scoped ModularForm PowerSeries

/-- Exact application checks for the standard integral model of `X₀(6)`
over `ℤ[1/6]`.  This is the permissible E7 boundary: it exposes the model and
its standard comparison laws but does not assume that the Hauptmodul is a
degree-one coordinate. -/
structure ActualX0SixApplicationChecks where
  Cusp : Type
  Curve : Type
  Divisor : Type
  M : SptCM.RolenLiterature.LigozatModel
    SptCM.CM.Repaired.LevelSixEtaExponents
    (UpperHalfPlane → ℂ) Cusp ℚ Curve
  G : SptCM.RolenLiterature.IntegralCurveFunctionGeometry
    (UpperHalfPlane → ℂ) Divisor Curve Cusp (PowerSeries ℤ)
  X : Curve
  zero : Cusp
  oneHalf : Cusp
  oneThird : Cusp
  infinity : Cusp
  ligozat : SptCM.RolenLiterature.LigozatEtaQuotients M
  integralModel : SptCM.RolenLiterature.X0SixGoodIntegralModel M
  genusZero : SptCM.RolenLiterature.X0SixGenusZeroFibers M
  disjointCusps : SptCM.RolenLiterature.X0SixDisjointCusps M
  horizontalDivisor :
    SptCM.RolenLiterature.E7HorizontalDivisorPrinciple G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.isModularFunction M.cuspOrder
  noVerticalComponent :
    SptCM.RolenLiterature.E7NoVerticalComponentPrinciple G
      M.isIntegralModelAwayFromLevel M.hasDisjointStandardCuspSections
  degreeOneCriterion :
    SptCM.RolenLiterature.E7IntegralDegreeOneCriterion G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.hasDisjointStandardCuspSections
  ligozatConditions :
    M.ligozatConditions SptCM.CM.Repaired.hauptmodulExponents
  levelSix : M.isLevelSixModularCurve X
  cuspCases : ∀ c : Cusp,
    c = zero ∨ c = oneHalf ∨ c = oneThird ∨ c = infinity
  quotient_eq_actual :
    M.quotient SptCM.CM.Repaired.hauptmodulExponents =
      SptCM.CM.Repaired.analyticHauptmodul
  order_zero :
    M.orderFormula SptCM.CM.Repaired.hauptmodulExponents zero =
      SptCM.CM.Repaired.ligozatCuspOrder
        SptCM.CM.Repaired.hauptmodulExponents 1
  order_oneHalf :
    M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneHalf =
      SptCM.CM.Repaired.ligozatCuspOrder
        SptCM.CM.Repaired.hauptmodulExponents 2
  order_oneThird :
    M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneThird =
      SptCM.CM.Repaired.ligozatCuspOrder
        SptCM.CM.Repaired.hauptmodulExponents 3
  order_infinity :
    M.orderFormula SptCM.CM.Repaired.hauptmodulExponents infinity =
      SptCM.CM.Repaired.ligozatCuspOrder
        SptCM.CM.Repaired.hauptmodulExponents 6
  analyticNonvanishingInterpretation :
    ∀ f : UpperHalfPlane → ℂ, (∀ τ, f τ ≠ 0) →
      G.hasNoInteriorZeroOrPole f X
  integralExpansionInterpretation :
    ∀ (f : UpperHalfPlane → ℂ) (u : PowerSeries ℤ),
      HasActualIntegralUnitExpansion f u →
        G.hasIntegralUnitExpansionAt f infinity u

/-- The proposition-valued exact E7 input: the standard integral model and
all comparison maps required by the application exist. -/
def E7ActualX0SixApplicationChecks : Prop :=
  Nonempty ActualX0SixApplicationChecks

/-- The paper's actual integral-coordinate assertion, expressed without
choosing implementation types for the standard integral modular curve. -/
def ActualHauptmodulIntegralCoordinate : Prop :=
  ∃ D : ActualX0SixApplicationChecks,
    D.G.identifiesWithProjectiveLine
      (D.M.quotient SptCM.CM.Repaired.hauptmodulExponents) D.X

/-- E7 plus the explicit Ligozat calculations, analytic nonvanishing, and
proved integral Euler expansion give the genuine degree-one coordinate.
The conclusion is not a field of `ActualX0SixApplicationChecks`. -/
theorem actualHauptmodul_integral_coordinate
    (D : ActualX0SixApplicationChecks) :
    D.G.identifiesWithProjectiveLine
      (D.M.quotient SptCM.CM.Repaired.hauptmodulExponents) D.X := by
  exact analyticHauptmodul_integral_coordinate_of_E7
    D.M D.G D.ligozat D.integralModel D.genusZero D.disjointCusps
    D.horizontalDivisor D.noVerticalComponent D.degreeOneCriterion
    D.X D.zero D.oneHalf D.oneThird D.infinity
    D.ligozatConditions D.levelSix
    ⟨D.order_zero, D.order_oneHalf, D.order_oneThird, D.order_infinity⟩
    D.cuspCases D.quotient_eq_actual
    D.analyticNonvanishingInterpretation D.integralExpansionInterpretation

/-- Proposition-valued paper-facing I15 conclusion from only the exact E7
standard-model input. -/
theorem exists_actualHauptmodul_integral_coordinate
    (hE7 : E7ActualX0SixApplicationChecks) :
    ActualHauptmodulIntegralCoordinate := by
  let D := Classical.choice hE7
  exact ⟨D, actualHauptmodul_integral_coordinate D⟩

end SptCM.Repair
