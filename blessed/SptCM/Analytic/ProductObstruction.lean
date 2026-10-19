import blessed.SptCM.Lemmas.Polynomial
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# From product identities to the polynomial Wronskian obstruction

This file formalizes the algebraic bridge used after reducing the normalized
Borcherds product modulo a prime.  The only remaining analytic input is the
statement that the reduced product has zero logarithmic derivative.  The
chain rule, cancellation of the Hauptmodul derivative, and injectivity of
substitution at a transcendental parameter are all proved here.
-/

namespace SptCM.Analytic

open Polynomial

/-- In characteristic `p`, every `p`-th power is killed by every derivation. -/
theorem derivation_pow_char_eq_zero
    {p : ℕ} {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [CharP A p]
    (D : Derivation R A A) (x : A) :
    D (x ^ p) = 0 := by
  rw [D.leibniz_pow]
  rw [← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

/-- Concrete power-series Frobenius consequence. -/
theorem powerSeries_derivative_pow_char_eq_zero
    {p : ℕ} (R : Type*) [CommRing R] [CharP R p]
    (f : PowerSeries R) :
    PowerSeries.derivative R (f ^ p) = 0 := by
  letI : CharP (PowerSeries R) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  exact derivation_pow_char_eq_zero (p := p) (R := R) (A := PowerSeries R)
    (PowerSeries.derivative R) f

/-- A power series supported on exponents divisible by the characteristic has
zero formal derivative.  This is the coefficientwise version of the
`q ↦ q^p` Frobenius phenomenon and does not require choosing a `p`-th root. -/
theorem powerSeries_derivative_eq_zero_of_support_dvd_char
    {p : ℕ} {R : Type*} [CommRing R] [CharP R p]
    (f : PowerSeries R)
    (hsupport : ∀ n : ℕ, ¬p ∣ n → PowerSeries.coeff n f = 0) :
    PowerSeries.derivative R f = 0 := by
  ext n
  rw [PowerSeries.coeff_derivative]
  by_cases hdiv : p ∣ n + 1
  · have hcast : ((n + 1 : ℕ) : R) = 0 :=
      (CharP.cast_eq_zero_iff R p (n + 1)).2 hdiv
    have hcast' : (n : R) + 1 = 0 := by simpa using hcast
    rw [hcast', mul_zero]
    simp
  · rw [hsupport (n + 1) hdiv]
    simp

/-- The chain-rule factorization of the cross derivative of two polynomial
specializations.  Its polynomial factor is exactly the convention
`A'B - AB'` used by `wronskianObstruction`. -/
theorem crossDerivative_aeval_eq_wronskianObstruction_mul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (D : Derivation R S S) (t : S) (A B : Polynomial R) :
    D (aeval t A) * aeval t B - aeval t A * D (aeval t B) =
      aeval t (SptCM.wronskianObstruction A B) * D t := by
  rw [D.comp_aeval_eq t A, D.comp_aeval_eq t B]
  simp only [smul_eq_mul, SptCM.wronskianObstruction, map_sub, map_mul, aeval_def]
  ring

/-- If the specialized quotient has zero cross derivative and `t'` is
nonzero, then the Wronskian obstruction vanishes after substitution. -/
theorem aeval_wronskianObstruction_eq_zero_of_crossDerivative_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [NoZeroDivisors S]
    [Algebra R S]
    (D : Derivation R S S) (t : S) (A B : Polynomial R)
    (ht : D t ≠ 0)
    (hcross : D (aeval t A) * aeval t B -
      aeval t A * D (aeval t B) = 0) :
    aeval t (SptCM.wronskianObstruction A B) = 0 := by
  rw [crossDerivative_aeval_eq_wronskianObstruction_mul D t A B] at hcross
  exact (mul_eq_zero.mp hcross).resolve_right ht

/-- The substitution step in the paper: transcendence of the Hauptmodul
parameter makes polynomial evaluation injective, hence the polynomial
Wronskian itself is zero. -/
theorem wronskianObstruction_eq_zero_of_crossDerivative_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [NoZeroDivisors S]
    [Algebra R S]
    (D : Derivation R S S) (t : S) (A B : Polynomial R)
    (htrans : Transcendental R t) (ht : D t ≠ 0)
    (hcross : D (aeval t A) * aeval t B -
      aeval t A * D (aeval t B) = 0) :
    SptCM.wronskianObstruction A B = 0 := by
  apply (transcendental_iff.mp htrans)
  exact aeval_wronskianObstruction_eq_zero_of_crossDerivative_eq_zero
    D t A B ht hcross

/-- The exact quotient-to-chain-rule bridge.  If `A(t) / B(t)` is represented
by a quotient `numerator / denominator` whose numerator and denominator are
killed by the derivation, then the cross derivative of `A(t), B(t)` vanishes.
This formulation avoids division and only asks that the displayed denominator
be nonzero. -/
theorem wronskianObstruction_eq_zero_of_zero_derivative_quotient
    {R S : Type*} [CommRing R] [CommRing S] [NoZeroDivisors S]
    [Algebra R S]
    (D : Derivation R S S) (t : S) (A B : Polynomial R)
    (htrans : Transcendental R t) (ht : D t ≠ 0)
    (numerator denominator : S)
    (hdenominator : denominator ≠ 0)
    (hquotient : aeval t A * denominator = numerator * aeval t B)
    (hnumerator : D numerator = 0) (hdenominator_deriv : D denominator = 0) :
    SptCM.wronskianObstruction A B = 0 := by
  apply wronskianObstruction_eq_zero_of_crossDerivative_eq_zero
    D t A B htrans ht
  have hderiv := congrArg D hquotient
  rw [D.leibniz, D.leibniz, hnumerator, hdenominator_deriv] at hderiv
  have hderiv' :
      D (aeval t A) * denominator = numerator * D (aeval t B) := by
    simpa [smul_eq_mul, mul_comm] using hderiv
  apply (mul_right_cancel₀ hdenominator)
  rw [zero_mul]
  calc
    (D (aeval t A) * aeval t B - aeval t A * D (aeval t B)) *
        denominator =
      (D (aeval t A) * denominator) * aeval t B -
        D (aeval t B) * (aeval t A * denominator) := by ring
    _ = (numerator * D (aeval t B)) * aeval t B -
        D (aeval t B) * (numerator * aeval t B) := by
          rw [hderiv', hquotient]
    _ = 0 := by ring

/-- A convenient product/Frobenius form: if both specialized class
polynomials differ from `p`-th powers by the same factor, their cross
derivative vanishes and hence so does the polynomial Wronskian. -/
theorem wronskianObstruction_eq_zero_of_common_factor_frobenius
    {p : ℕ} {R S : Type*} [CommRing R] [CommRing S] [NoZeroDivisors S]
    [Algebra R S] [CharP S p]
    (D : Derivation R S S) (t : S) (A B : Polynomial R)
    (htrans : Transcendental R t) (ht : D t ≠ 0)
    (u F G : S)
    (hA : aeval t A = u * F ^ p)
    (hB : aeval t B = u * G ^ p) :
    SptCM.wronskianObstruction A B = 0 := by
  apply wronskianObstruction_eq_zero_of_crossDerivative_eq_zero
    D t A B htrans ht
  rw [hA, hB]
  rw [D.leibniz, D.leibniz, derivation_pow_char_eq_zero D F,
    derivation_pow_char_eq_zero D G]
  ring

end SptCM.Analytic
