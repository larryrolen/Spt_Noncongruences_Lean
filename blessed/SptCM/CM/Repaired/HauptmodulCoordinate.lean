import blessed.SptCM.Literature.RolenLiterature
import blessed.SptCM.CM.ClassPolynomials
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# The level-six eta quotient: finite Ligozat calculations

This file isolates the completely finite part of I15.  For

`t(τ) = η(τ)^5 η(3τ) / (η(2τ) η(6τ)^5)`

the exponent vector is `(5,-1,1,-5)`, indexed by `1,2,3,6`.  We calculate
the weight, both Ligozat congruence sums, the square character parameter, and
all four cusp orders.  The final section states separately the residual
geometric principle needed to turn this divisor calculation into an
isomorphism of integral curves; the isomorphism is not assumed as an
arithmetic input.
-/

namespace SptCM.CM.Repaired

open SptCM.RolenLiterature

/-- Rolen's analytic Hauptmodul using Mathlib's actual Dedekind eta
function, rather than an arbitrary function named `eta`. -/
noncomputable def analyticHauptmodul (τ : UpperHalfPlane) : ℂ :=
  SptCM.hauptmodul ModularForm.eta τ

/-- Every positive integral multiple of a point in the upper half-plane is
again in the upper half-plane. -/
private theorem nat_mul_mem_upperHalfPlaneSet
    (m : ℕ) (hm : 0 < m) (τ : UpperHalfPlane) :
    (m : ℂ) * (τ : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
  change 0 < (((m : ℂ) * (τ : ℂ)).im)
  simpa [Complex.mul_im] using
    mul_pos (Nat.cast_pos.2 hm : (0 : ℝ) < m) τ.im_pos

/-- The eta quotient has no zero or pole in the open upper half-plane.  This
discharges the analytic ``no interior zero'' calculation in I15 directly
from Mathlib's theorem `ModularForm.eta_ne_zero`; only the cusp and integral
model geometry remains in E7's application. -/
theorem analyticHauptmodul_ne_zero (τ : UpperHalfPlane) :
    analyticHauptmodul τ ≠ 0 := by
  unfold analyticHauptmodul SptCM.hauptmodul
  apply div_ne_zero
  · exact mul_ne_zero
      (pow_ne_zero 5 (ModularForm.eta_ne_zero τ.2))
      (ModularForm.eta_ne_zero
        (nat_mul_mem_upperHalfPlaneSet 3 (by norm_num) τ))
  · exact mul_ne_zero
      (ModularForm.eta_ne_zero
        (nat_mul_mem_upperHalfPlaneSet 2 (by norm_num) τ))
      (pow_ne_zero 5 (ModularForm.eta_ne_zero
        (nat_mul_mem_upperHalfPlaneSet 6 (by norm_num) τ)))

/-- An eta-exponent vector at the four divisors of level six. -/
structure LevelSixEtaExponents where
  atOne : ℤ
  atTwo : ℤ
  atThree : ℤ
  atSix : ℤ

/-- The exponent vector of Rolen's Hauptmodul. -/
def hauptmodulExponents : LevelSixEtaExponents :=
  ⟨5, -1, 1, -5⟩

/-- Twice the eta-quotient weight. -/
def etaWeightNumerator (e : LevelSixEtaExponents) : ℤ :=
  e.atOne + e.atTwo + e.atThree + e.atSix

/-- The first Ligozat congruence sum `Σ δ r_δ`. -/
def firstLigozatSum (e : LevelSixEtaExponents) : ℤ :=
  e.atOne + 2 * e.atTwo + 3 * e.atThree + 6 * e.atSix

/-- The second Ligozat congruence sum `Σ (6/δ) r_δ`. -/
def secondLigozatSum (e : LevelSixEtaExponents) : ℤ :=
  6 * e.atOne + 3 * e.atTwo + 2 * e.atThree + e.atSix

@[simp] theorem hauptmodul_weight_numerator :
    etaWeightNumerator hauptmodulExponents = 0 := by
  norm_num [etaWeightNumerator, hauptmodulExponents]

@[simp] theorem hauptmodul_first_ligozat_sum :
    firstLigozatSum hauptmodulExponents = -24 := by
  norm_num [firstLigozatSum, hauptmodulExponents]

@[simp] theorem hauptmodul_second_ligozat_sum :
    secondLigozatSum hauptmodulExponents = 24 := by
  norm_num [secondLigozatSum, hauptmodulExponents]

/-- The rational character parameter
`∏ δ^{r_δ} = 2⁻⁶3⁻⁴`. -/
def hauptmodulCharacterParameter : ℚ :=
  1 / (2 ^ 6 * 3 ^ 4)

/-- The character parameter is the square `(1/72)^2`; this is the finite
calculation behind triviality of the eta-quotient character. -/
theorem hauptmodul_character_parameter_isSquare :
    hauptmodulCharacterParameter = (1 / 72 : ℚ) ^ 2 := by
  norm_num [hauptmodulCharacterParameter]

/-- Ligozat's order formula at the cusp represented by denominator `c ∣ 6`.
The four summands are indexed by `δ = 1,2,3,6`. -/
def ligozatCuspOrder (e : LevelSixEtaExponents) (c : ℕ) : ℚ :=
  (6 : ℚ) / 24 *
    (((Nat.gcd c 1 : ℚ) ^ 2 * e.atOne) /
        (Nat.gcd c (6 / c) * c * 1 : ℕ) +
      ((Nat.gcd c 2 : ℚ) ^ 2 * e.atTwo) /
        (Nat.gcd c (6 / c) * c * 2 : ℕ) +
      ((Nat.gcd c 3 : ℚ) ^ 2 * e.atThree) /
        (Nat.gcd c (6 / c) * c * 3 : ℕ) +
      ((Nat.gcd c 6 : ℚ) ^ 2 * e.atSix) /
        (Nat.gcd c (6 / c) * c * 6 : ℕ))

/-- The order at the cusp `0` (denominator `1`) is one. -/
@[simp] theorem hauptmodul_order_at_zero :
    ligozatCuspOrder hauptmodulExponents 1 = 1 := by
  norm_num [ligozatCuspOrder, hauptmodulExponents]

/-- The order at the cusp `1/2` is zero. -/
@[simp] theorem hauptmodul_order_at_oneHalf :
    ligozatCuspOrder hauptmodulExponents 2 = 0 := by
  norm_num [ligozatCuspOrder, hauptmodulExponents]

/-- The order at the cusp `1/3` is zero. -/
@[simp] theorem hauptmodul_order_at_oneThird :
    ligozatCuspOrder hauptmodulExponents 3 = 0 := by
  norm_num [ligozatCuspOrder, hauptmodulExponents]

/-- The order at the cusp `∞` (denominator `6`) is minus one. -/
@[simp] theorem hauptmodul_order_at_infinity :
    ligozatCuspOrder hauptmodulExponents 6 = -1 := by
  norm_num [ligozatCuspOrder, hauptmodulExponents]

/-- The complete finite arithmetic output of the Ligozat calculation. -/
theorem hauptmodul_finite_ligozat_calculations :
    etaWeightNumerator hauptmodulExponents = 0 ∧
    firstLigozatSum hauptmodulExponents = -24 ∧
    secondLigozatSum hauptmodulExponents = 24 ∧
    hauptmodulCharacterParameter = (1 / 72 : ℚ) ^ 2 ∧
    ligozatCuspOrder hauptmodulExponents 1 = 1 ∧
    ligozatCuspOrder hauptmodulExponents 2 = 0 ∧
    ligozatCuspOrder hauptmodulExponents 3 = 0 ∧
    ligozatCuspOrder hauptmodulExponents 6 = -1 := by
  simp [hauptmodul_character_parameter_isSquare]

/-! ## Residual integral geometry

The remaining arguments are expressed using E7's general geometric laws,
not a record containing paper-specific conclusions.  The hypotheses below
are the precise bridges which are not supplied by the abstract `LigozatModel`:
the standard cusp labeling, the no-interior-zero-or-pole statement, and
identification of the analytic
Laurent expansion with an integral unit expansion. -/

/-- E7 and the four explicit order calculations give the horizontal divisor
`[0]-[∞]`.  The two middle cusps have order zero, while `hcusps` says that
these are all standard cusps. -/
theorem hauptmodul_horizontal_divisor_of_E7
    {Function Cusp Curve Divisor Expansion : Type*}
    (M : LigozatModel LevelSixEtaExponents Function Cusp ℚ Curve)
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Cusp Expansion)
    (hLigozat : LigozatEtaQuotients M)
    (hIntegral : X0SixGoodIntegralModel M)
    (hGenusZero : X0SixGenusZeroFibers M)
    (hHorizontal : E7HorizontalDivisorPrinciple G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.isModularFunction M.cuspOrder)
    (X : Curve) (zero oneHalf oneThird infinity : Cusp)
    (hconditions : M.ligozatConditions hauptmodulExponents)
    (hlevel : M.isLevelSixModularCurve X)
    (hinterior :
      G.hasNoInteriorZeroOrPole (M.quotient hauptmodulExponents) X)
    (horders :
      M.orderFormula hauptmodulExponents zero =
          ligozatCuspOrder hauptmodulExponents 1 ∧
      M.orderFormula hauptmodulExponents oneHalf =
          ligozatCuspOrder hauptmodulExponents 2 ∧
      M.orderFormula hauptmodulExponents oneThird =
          ligozatCuspOrder hauptmodulExponents 3 ∧
      M.orderFormula hauptmodulExponents infinity =
          ligozatCuspOrder hauptmodulExponents 6)
    (hcusps : ∀ c : Cusp,
      c = zero ∨ c = oneHalf ∨ c = oneThird ∨ c = infinity) :
    G.divisor (M.quotient hauptmodulExponents) =
      G.sectionDifference X zero infinity := by
  have htheorem := hLigozat hauptmodulExponents hconditions
  have hformula := htheorem.2.1
  have hintegral := hIntegral X hlevel
  have hgenus := hGenusZero X hlevel
  apply hHorizontal X (M.quotient hauptmodulExponents) zero infinity
    hintegral hgenus htheorem.1 hinterior
  · rw [hformula zero, horders.1]
    exact hauptmodul_order_at_zero
  · rw [hformula infinity, horders.2.2.2]
    exact hauptmodul_order_at_infinity
  · intro c hcz hci
    rcases hcusps c with rfl | rfl | rfl | rfl
    · exact (hcz rfl).elim
    · rw [hformula _, horders.2.1]
      exact hauptmodul_order_at_oneHalf
    · rw [hformula _, horders.2.2.1]
      exact hauptmodul_order_at_oneThird
    · exact (hci rfl).elim

/-- An actual integral unit expansion at infinity, together with the
horizontal divisor and E7's good-model/disjoint-cusp facts, excludes vertical
components.  Notice that the expansion is an explicit hypothesis: the
independently constructed formal Euler product does not by itself identify
the analytic eta quotient's expansion. -/
theorem hauptmodul_no_vertical_component_of_E7
    {Function Cusp Curve Divisor Expansion Exponent Order : Type*}
    (M : LigozatModel Exponent Function Cusp Order Curve)
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Cusp Expansion)
    (hIntegral : X0SixGoodIntegralModel M)
    (hCusps : X0SixDisjointCusps M)
    (hNoVertical : E7NoVerticalComponentPrinciple G
      M.isIntegralModelAwayFromLevel M.hasDisjointStandardCuspSections)
    (X : Curve) (f : Function) (zero infinity : Cusp)
    (expansion : Expansion)
    (hlevel : M.isLevelSixModularCurve X)
    (hdivisor : G.divisor f = G.sectionDifference X zero infinity)
    (hexpansion : G.hasIntegralUnitExpansionAt f infinity expansion) :
    G.hasNoVerticalComponent f X :=
  hNoVertical X f zero infinity expansion
    (hIntegral X hlevel) (hCusps X hlevel) hdivisor hexpansion

/-- The genuinely general E7 degree-one law turns the derived divisor and
absence of vertical components into an integral coordinate. -/
theorem integral_degree_one_coordinate_of_E7
    {Function Cusp Curve Divisor Expansion Exponent Order : Type*}
    (M : LigozatModel Exponent Function Cusp Order Curve)
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Cusp Expansion)
    (hIntegral : X0SixGoodIntegralModel M)
    (hGenusZero : X0SixGenusZeroFibers M)
    (hCusps : X0SixDisjointCusps M)
    (hDegreeOne : E7IntegralDegreeOneCriterion G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.hasDisjointStandardCuspSections)
    (X : Curve) (f : Function) (zero infinity : Cusp)
    (hlevel : M.isLevelSixModularCurve X)
    (hdivisor : G.divisor f = G.sectionDifference X zero infinity)
    (hvertical : G.hasNoVerticalComponent f X) :
    G.identifiesWithProjectiveLine f X :=
  hDegreeOne X f zero infinity
    (hIntegral X hlevel) (hGenusZero X hlevel) (hCusps X hlevel)
    hdivisor hvertical

/-- Conditional final I15 assembly.  Every input is a named mathematical
fact rather than a field of an application record.  In particular,
`hexpansion` is the still-required analytic/formal bridge. -/
theorem hauptmodul_integral_coordinate_of_E7
    {Function Cusp Curve Divisor Expansion : Type*}
    (M : LigozatModel LevelSixEtaExponents Function Cusp ℚ Curve)
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Cusp Expansion)
    (hLigozat : LigozatEtaQuotients M)
    (hIntegral : X0SixGoodIntegralModel M)
    (hGenusZero : X0SixGenusZeroFibers M)
    (hCusps : X0SixDisjointCusps M)
    (hHorizontal : E7HorizontalDivisorPrinciple G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.isModularFunction M.cuspOrder)
    (hNoVertical : E7NoVerticalComponentPrinciple G
      M.isIntegralModelAwayFromLevel M.hasDisjointStandardCuspSections)
    (hDegreeOne : E7IntegralDegreeOneCriterion G
      M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers
      M.hasDisjointStandardCuspSections)
    (X : Curve) (zero oneHalf oneThird infinity : Cusp)
    (expansion : Expansion)
    (hconditions : M.ligozatConditions hauptmodulExponents)
    (hlevel : M.isLevelSixModularCurve X)
    (hinterior :
      G.hasNoInteriorZeroOrPole (M.quotient hauptmodulExponents) X)
    (horders :
      M.orderFormula hauptmodulExponents zero =
          ligozatCuspOrder hauptmodulExponents 1 ∧
      M.orderFormula hauptmodulExponents oneHalf =
          ligozatCuspOrder hauptmodulExponents 2 ∧
      M.orderFormula hauptmodulExponents oneThird =
          ligozatCuspOrder hauptmodulExponents 3 ∧
      M.orderFormula hauptmodulExponents infinity =
          ligozatCuspOrder hauptmodulExponents 6)
    (hcuspCases : ∀ c : Cusp,
      c = zero ∨ c = oneHalf ∨ c = oneThird ∨ c = infinity)
    (hexpansion : G.hasIntegralUnitExpansionAt
      (M.quotient hauptmodulExponents) infinity expansion) :
    G.identifiesWithProjectiveLine
      (M.quotient hauptmodulExponents) X := by
  have hdivisor := hauptmodul_horizontal_divisor_of_E7 M G
    hLigozat hIntegral hGenusZero hHorizontal X zero oneHalf oneThird
    infinity hconditions hlevel hinterior horders hcuspCases
  have hvertical := hauptmodul_no_vertical_component_of_E7 M G
    hIntegral hCusps hNoVertical X (M.quotient hauptmodulExponents)
    zero infinity expansion hlevel hdivisor hexpansion
  exact integral_degree_one_coordinate_of_E7 M G hIntegral hGenusZero
    hCusps hDegreeOne X (M.quotient hauptmodulExponents) zero infinity
    hlevel hdivisor hvertical

end SptCM.CM.Repaired
