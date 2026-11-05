module

public import blessed.SptCM.CM.ClassPolynomials
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Reduction of the oriented class polynomials

The CM values defining the characteristic-zero class polynomials need not
reduce to the prime field.  This module keeps the polynomial coefficients over
`ℤ[1/6]`, reduces those coefficients to `ZMod ℓ`, and places roots in an
arbitrary algebraically closed extension.  In particular it does not make the
incorrect assertion that every reduced CM value belongs to `ZMod ℓ`.
-/

namespace SptCM

noncomputable section

open Polynomial

/-- The coefficient ring `ℤ[1/6]` used by the oriented class polynomials. -/
abbrev AwaySix := Localization.Away (6 : ℤ)

/-- Reduction of coefficients in `ℤ[1/6]` to a field of characteristic `ℓ`.
The explicit unit hypothesis is precisely the good-prime condition needed by
the universal property of localization. -/
@[expose]
def awaySixReduction (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ)) :
    AwaySix →+* ZMod ℓ :=
  Localization.awayLift (Int.castRingHom (ZMod ℓ)) 6 (by simpa using h6)

/-- At every prime in the range of the paper, reduction modulo `ℓ` is defined
on `ℤ[1/6]`. -/
theorem six_isUnit_zmod_of_prime_five_le {ℓ : ℕ}
    (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ) :
    IsUnit (6 : ZMod ℓ) := by
  change IsUnit ((6 : ℕ) : ZMod ℓ)
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.symm
  rw [hprime.coprime_iff_not_dvd]
  intro hdvd
  have hle : ℓ ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases ℓ
  · norm_num at hdvd
  · norm_num at hprime

/-- An oriented pair of class polynomials before reduction. -/
structure IntegralOrientedClassPolynomials (n : ℕ) where
  numerator : AwaySix[X]
  denominator : AwaySix[X]
  numerator_monic : numerator.Monic
  denominator_monic : denominator.Monic

/-- Coefficientwise reduction of the numerator polynomial. -/
@[expose]
def IntegralOrientedClassPolynomials.reduceNumerator
    {n ℓ : ℕ} (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) : (ZMod ℓ)[X] :=
  P.numerator.map (awaySixReduction ℓ h6)

/-- Coefficientwise reduction of the denominator polynomial. -/
@[expose]
def IntegralOrientedClassPolynomials.reduceDenominator
    {n ℓ : ℕ} (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) : (ZMod ℓ)[X] :=
  P.denominator.map (awaySixReduction ℓ h6)

/-- Coefficient reduction preserves numerator monicity. -/
theorem IntegralOrientedClassPolynomials.reduceNumerator_monic
    {n ℓ : ℕ} (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) :
    (P.reduceNumerator h6).Monic :=
  P.numerator_monic.map _

/-- Coefficient reduction preserves denominator monicity. -/
theorem IntegralOrientedClassPolynomials.reduceDenominator_monic
    {n ℓ : ℕ} (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) :
    (P.reduceDenominator h6).Monic :=
  P.denominator_monic.map _

/-- A common reduced root is correctly sought in an algebraically closed
extension of `ZMod ℓ`, not necessarily in `ZMod ℓ` itself. -/
@[expose]
def HasReducedCMCollision {n ℓ : ℕ}
    (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod ℓ) K)
      (_ : IsAlgClosed K) (x : K),
    aeval x (P.reduceNumerator h6) = 0 ∧
      aeval x (P.reduceDenominator h6) = 0

/-- The collision predicate is witnessed by a root in any chosen
algebraically closed coefficient extension. -/
theorem hasReducedCMCollision_of_common_root
    {n ℓ : ℕ} (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {K : Type} [Field K] [Algebra (ZMod ℓ) K] [IsAlgClosed K]
    {x : K}
    (hA : aeval x (P.reduceNumerator h6) = 0)
    (hB : aeval x (P.reduceDenominator h6) = 0) :
    HasReducedCMCollision P h6 :=
  ⟨K, inferInstance, inferInstance, inferInstance, x, hA, hB⟩

/-- Failure of coprimality of the reduced class polynomials is exactly a
collision over an algebraically closed extension.  This is the algebraic
replacement for the incorrect requirement that both roots be elements of the
prime field. -/
theorem not_isCoprime_reductions_iff_collision
    {n ℓ : ℕ} [Fact ℓ.Prime]
    (P : IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ)) :
    ¬ IsCoprime (P.reduceNumerator h6) (P.reduceDenominator h6) ↔
      HasReducedCMCollision P h6 := by
  constructor
  · intro hnot
    have hroot :
        ∃ x : AlgebraicClosure (ZMod ℓ),
          aeval x (P.reduceNumerator h6) = 0 ∧
            aeval x (P.reduceDenominator h6) = 0 := by
      rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))] at hnot
      push_neg at hnot
      exact hnot
    obtain ⟨x, hA, hB⟩ := hroot
    exact hasReducedCMCollision_of_common_root P h6 hA hB
  · rintro ⟨K, hfield, halgebra, hclosed, x, hA, hB⟩ hcop
    letI : Field K := hfield
    letI : Algebra (ZMod ℓ) K := halgebra
    letI : IsAlgClosed K := hclosed
    have hne :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (ZMod ℓ) K (P.reduceNumerator h6) (P.reduceDenominator h6)).mp hcop x
    exact hne.elim (fun h => h hA) (fun h => h hB)

end

end SptCM
