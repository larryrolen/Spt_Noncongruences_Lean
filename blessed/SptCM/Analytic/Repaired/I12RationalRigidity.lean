module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic

@[expose] public section

namespace SptCM.Analytic.Repaired

open Polynomial

noncomputable section

/-- The full finite divisor of a rational function in the Hauptmodul
coordinate. The argument is the actual complex point, not its orientation.
The zero function is excluded whenever this divisor is used for rigidity. -/
def rationalFunctionDivisor (f : RatFunc ℚ) (z : ℂ) : ℤ :=
  ((f.num.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) -
    ((f.denom.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ)

/-- Cancellation of common factors does not change the signed divisor. -/
theorem rationalFunctionDivisor_div (p q : ℚ[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    rationalFunctionDivisor
      (algebraMap ℚ[X] (RatFunc ℚ) p / algebraMap ℚ[X] (RatFunc ℚ) q) =
      fun z => ((p.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) -
        ((q.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) := by
  let f : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) p /
    algebraMap ℚ[X] (RatFunc ℚ) q
  have hf : f ≠ 0 := div_ne_zero
    (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have hc : f.num * q = p * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl
  funext z
  have hm := congrArg (fun a : ℚ[X] =>
    (a.map (algebraMap ℚ ℂ)).rootMultiplicity z) hc
  simp only [Polynomial.map_mul] at hm
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero
    (Polynomial.map_ne_zero (RatFunc.num_ne_zero hf)) (Polynomial.map_ne_zero hq)),
    Polynomial.rootMultiplicity_mul (mul_ne_zero
      (Polynomial.map_ne_zero hp) (Polynomial.map_ne_zero f.denom_ne_zero))] at hm
  change ((f.num.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) -
    ((f.denom.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) = _
  omega

/-- Equal complex root multisets determine rational polynomials up to their
leading coefficients. This includes every root with its multiplicity. -/
theorem polynomial_proportional_of_complex_roots
    (p q : ℚ[X])
    (h : (p.map (algebraMap ℚ ℂ)).roots =
      (q.map (algebraMap ℚ ℂ)).roots) :
    C q.leadingCoeff * p = C p.leadingCoeff * q := by
  apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  simp only [Polynomial.map_mul, Polynomial.map_C]
  have hp := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p.map (algebraMap ℚ ℂ)))
  have hq := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := q.map (algebraMap ℚ ℂ)))
  rw [Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ ℂ).injective] at hp hq
  rw [← hp, ← hq, h]
  ring

/-- Divisors at all finite points, unlike four orientation counts, determine
a nonzero rational function up to a nonzero rational scalar. -/
theorem rationalFunction_divisor_rigidity
    (f g : RatFunc ℚ) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : rationalFunctionDivisor f = rationalFunctionDivisor g) :
    ∃ c : ℚ, c ≠ 0 ∧ f = algebraMap ℚ (RatFunc ℚ) c * g := by
  let p : ℚ[X] := f.num * g.denom
  let q : ℚ[X] := g.num * f.denom
  have hp : p ≠ 0 := mul_ne_zero (RatFunc.num_ne_zero hf) g.denom_ne_zero
  have hq : q ≠ 0 := mul_ne_zero (RatFunc.num_ne_zero hg) f.denom_ne_zero
  have hroots : (p.map (algebraMap ℚ ℂ)).roots =
      (q.map (algebraMap ℚ ℂ)).roots := by
    classical
    apply Multiset.ext.mpr
    intro z
    have hz := congrFun h z
    simp only [rationalFunctionDivisor] at hz
    simp only [p, q, Polynomial.map_mul]
    rw [Polynomial.roots_mul (mul_ne_zero
      (Polynomial.map_ne_zero (RatFunc.num_ne_zero hf))
      (Polynomial.map_ne_zero g.denom_ne_zero)),
      Polynomial.roots_mul (mul_ne_zero
        (Polynomial.map_ne_zero (RatFunc.num_ne_zero hg))
        (Polynomial.map_ne_zero f.denom_ne_zero))]
    simp only [Multiset.count_add, Polynomial.count_roots]
    omega
  have hpoly := polynomial_proportional_of_complex_roots p q hroots
  have hpLC : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqLC : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  refine ⟨p.leadingCoeff / q.leadingCoeff, div_ne_zero hpLC hqLC, ?_⟩
  have heq := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hpoly
  simp only [map_mul, RatFunc.algebraMap_C] at heq
  have hfd := RatFunc.num_div_denom f
  have hgd := RatFunc.num_div_denom g
  rw [← hfd, ← hgd]
  rw [map_div₀]
  have hqC : algebraMap ℚ (RatFunc ℚ) q.leadingCoeff ≠ 0 :=
    (map_ne_zero (algebraMap ℚ (RatFunc ℚ))).mpr hqLC
  have hfd0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hgd0 := RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have heq' : algebraMap ℚ (RatFunc ℚ) q.leadingCoeff *
    (algebraMap ℚ[X] (RatFunc ℚ) f.num * algebraMap ℚ[X] (RatFunc ℚ) g.denom) =
    algebraMap ℚ (RatFunc ℚ) p.leadingCoeff *
    (algebraMap ℚ[X] (RatFunc ℚ) g.num * algebraMap ℚ[X] (RatFunc ℚ) f.denom) := by
      have hcmap : (RatFunc.C : ℚ →+* RatFunc ℚ) =
          algebraMap ℚ (RatFunc ℚ) := Subsingleton.elim _ _
      simpa only [p, q, map_mul, hcmap] using heq
  field_simp
  linear_combination heq'

end

end SptCM.Analytic.Repaired
