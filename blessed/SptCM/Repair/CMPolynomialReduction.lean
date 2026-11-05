module

public import blessed.SptCM.CM.Reduction

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Repair I17: coefficient reduction and geometric roots

A CM class polynomial is first formed over `ℤ[1/6]`; only its coefficients are
then reduced to the prime field.  Its geometric roots live in an arbitrary
algebraically closed extension of that field.  No root is asserted to be
`ZMod ℓ`-rational.
-/

namespace SptCM.Repair

noncomputable section

open Polynomial

/-- Coefficientwise reduction of any polynomial over `ℤ[1/6]`. -/
@[expose]
def reduceAwaySixPolynomial (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    (P : SptCM.AwaySix[X]) : (ZMod ℓ)[X] :=
  P.map (SptCM.awaySixReduction ℓ h6)

/-- Reduction really acts coefficient by coefficient. -/
theorem coeff_reduceAwaySixPolynomial
    (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    (P : SptCM.AwaySix[X]) (i : ℕ) :
    (reduceAwaySixPolynomial ℓ h6 P).coeff i =
      SptCM.awaySixReduction ℓ h6 (P.coeff i) := by
  simp [reduceAwaySixPolynomial]

/-- Monicity is preserved by the coefficient reduction map. -/
theorem reduceAwaySixPolynomial_monic
    (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    {P : SptCM.AwaySix[X]} (hP : P.Monic) :
    (reduceAwaySixPolynomial ℓ h6 P).Monic := by
  exact hP.map _

/-- A geometric root of a reduced polynomial.  The algebraically closed field
`K` may be a genuine extension of `ZMod ℓ`. -/
@[expose]
def IsGeometricReducedRoot
    (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    (P : SptCM.AwaySix[X])
    {K : Type} [Field K] [Algebra (ZMod ℓ) K] [IsAlgClosed K]
    (x : K) : Prop :=
  aeval x (reduceAwaySixPolynomial ℓ h6 P) = 0

/-- The corrected common-root predicate for the two oriented CM class
polynomials. -/
@[expose]
def HasGeometricCMCollision
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod ℓ) K)
      (_ : IsAlgClosed K) (x : K),
    IsGeometricReducedRoot ℓ h6 P.numerator x ∧
      IsGeometricReducedRoot ℓ h6 P.denominator x

/-- The complete corrected reduction specification for a pair of integral
oriented class polynomials. -/
@[expose]
def RootReductionSpec
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) : Prop :=
  reduceAwaySixPolynomial ℓ h6 P.numerator =
      P.reduceNumerator h6 ∧
    reduceAwaySixPolynomial ℓ h6 P.denominator =
      P.reduceDenominator h6 ∧
    (¬ IsCoprime (P.reduceNumerator h6) (P.reduceDenominator h6) ↔
      HasGeometricCMCollision P h6)

/-- The repaired predicate agrees with the base reduction module's collision
predicate, so downstream code can migrate without changing its mathematics. -/
theorem hasGeometricCMCollision_iff
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) :
    HasGeometricCMCollision P h6 ↔ SptCM.HasReducedCMCollision P h6 := by
  rfl

/-- A common geometric root in any chosen algebraically closed extension
witnesses the corrected collision predicate. -/
theorem hasGeometricCMCollision_of_common_root
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {K : Type} [Field K] [Algebra (ZMod ℓ) K] [IsAlgClosed K]
    {x : K}
    (hA : IsGeometricReducedRoot ℓ h6 P.numerator x)
    (hB : IsGeometricReducedRoot ℓ h6 P.denominator x) :
    HasGeometricCMCollision P h6 :=
  ⟨K, inferInstance, inferInstance, inferInstance, x, hA, hB⟩

/-- I17: at a prime in the paper's range, coefficientwise reduction and the
algebraic-closure common-root criterion satisfy the complete repaired
specification. -/
theorem rootReductionSpec_of_prime
    {n ℓ : ℕ} [Fact ℓ.Prime]
    (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) :
    RootReductionSpec P h6 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [hasGeometricCMCollision_iff]
  exact SptCM.not_isCoprime_reductions_iff_collision P h6

end

end SptCM.Repair
