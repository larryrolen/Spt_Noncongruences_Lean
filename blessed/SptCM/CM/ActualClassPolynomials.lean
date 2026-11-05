module

public import blessed.SptCM.CM.Reduction

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Class polynomials indexed by the actual oriented form classes

This module replaces the unconstrained finite index types of the original
endpoint by finite enumerations equivalent to the concrete quotient
`orientedForms n r`.  The existence and cardinality of those enumerations is a
standard CM/class-group input; once supplied, the class-polynomial
construction and its degree calculation are internal algebra.
-/

namespace SptCM

noncomputable section

open Polynomial

local instance awaySixIsDomain : IsDomain AwaySix :=
  Localization.Away.isDomain (by norm_num)

/-- The canonical embedding of `ℤ[1/6]` into the complex numbers. -/
@[expose]
def awaySixToComplex : AwaySix →+* ℂ :=
  Localization.awayLift (Int.castRingHom ℂ) 6 (by
    apply isUnit_iff_ne_zero.mpr
    norm_num)

/-- A finite enumeration of the actual `Γ₀(6)`-oriented quadratic-form
classes of discriminant `-n` and orientation `r`. -/
structure OrientedCMEnumeration (n r h : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  classes : Index ≃ orientedForms n r
  card_eq : Fintype.card Index = h

attribute [instance] OrientedCMEnumeration.indexFintype

/-- Integral Hauptmodul coordinates on each of the four actual orientation
classes.  Their existence is obtained from the integral-coordinate and
standard CM theorems; the polynomial construction below does not assume any
root lies in a residue prime field. -/
structure OrientedCMIntegralCoordinates (n h : ℕ) where
  orientation1 : OrientedCMEnumeration n 1 h
  orientation11 : OrientedCMEnumeration n 11 h
  orientation5 : OrientedCMEnumeration n 5 h
  orientation7 : OrientedCMEnumeration n 7 h
  coordinate1 : orientedForms n 1 → AwaySix
  coordinate11 : orientedForms n 11 → AwaySix
  coordinate5 : orientedForms n 5 → AwaySix
  coordinate7 : orientedForms n 7 → AwaySix

/-- Analytic realization of the integral coordinates as the actual eta
quotient at the four families of CM points. -/
structure OrientedCMAnalyticRealization (n h : ℕ)
    extends OrientedCMIntegralCoordinates n h where
  eta : ℂ → ℂ
  cmPoint1 : orientedForms n 1 → ℂ
  cmPoint11 : orientedForms n 11 → ℂ
  cmPoint5 : orientedForms n 5 → ℂ
  cmPoint7 : orientedForms n 7 → ℂ
  realizes1 : ∀ Q,
    awaySixToComplex (coordinate1 Q) = hauptmodul eta (cmPoint1 Q)
  realizes11 : ∀ Q,
    awaySixToComplex (coordinate11 Q) = hauptmodul eta (cmPoint11 Q)
  realizes5 : ∀ Q,
    awaySixToComplex (coordinate5 Q) = hauptmodul eta (cmPoint5 Q)
  realizes7 : ∀ Q,
    awaySixToComplex (coordinate7 Q) = hauptmodul eta (cmPoint7 Q)

namespace OrientedCMIntegralCoordinates

variable {n h : ℕ} (D : OrientedCMIntegralCoordinates n h)

/-- The actual numerator polynomial, using orientations `1` and `11`. -/
@[expose]
def numeratorPolynomial : AwaySix[X] :=
  classPolyA
    (fun i : D.orientation1.Index =>
      D.coordinate1 (D.orientation1.classes i))
    (fun i : D.orientation11.Index =>
      D.coordinate11 (D.orientation11.classes i))

/-- The actual denominator polynomial, using orientations `5` and `7`. -/
@[expose]
def denominatorPolynomial : AwaySix[X] :=
  classPolyB
    (fun i : D.orientation5.Index =>
      D.coordinate5 (D.orientation5.classes i))
    (fun i : D.orientation7.Index =>
      D.coordinate7 (D.orientation7.classes i))

/-- The numerator constructed from the actual orientation classes is monic. -/
theorem numeratorPolynomial_monic : D.numeratorPolynomial.Monic :=
  classPolyA_monic _ _

/-- The denominator constructed from the actual orientation classes is
monic. -/
theorem denominatorPolynomial_monic : D.denominatorPolynomial.Monic :=
  classPolyB_monic _ _

/-- Both numerator orientation sets have cardinality `h`, so the numerator
has degree `2h`. -/
theorem numeratorPolynomial_natDegree :
    D.numeratorPolynomial.natDegree = 2 * h :=
  classPolyA_natDegree _ _ h
    D.orientation1.card_eq D.orientation11.card_eq

/-- Both denominator orientation sets have cardinality `h`, so the
denominator has degree `2h`. -/
theorem denominatorPolynomial_natDegree :
    D.denominatorPolynomial.natDegree = 2 * h :=
  classPolyB_natDegree _ _ h
    D.orientation5.card_eq D.orientation7.card_eq

/-- Package the two characteristic-zero polynomials with their internally
proved monicity. -/
@[expose]
def integralPolynomials : IntegralOrientedClassPolynomials n where
  numerator := D.numeratorPolynomial
  denominator := D.denominatorPolynomial
  numerator_monic := D.numeratorPolynomial_monic
  denominator_monic := D.denominatorPolynomial_monic

/-- The canonical coefficientwise reductions of the two actual oriented
class polynomials at a prime away from the level.  Keeping the pair in this
order matches the numerator/denominator convention used by the Wronskian. -/
@[expose]
def reducedClassPolynomials
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (ZMod ℓ)[X] × (ZMod ℓ)[X] :=
  (D.integralPolynomials.reduceNumerator h6,
    D.integralPolynomials.reduceDenominator h6)

/-- Complete arithmetic specification of the two actual characteristic-zero
class polynomials: their coefficient ring already records integrality away
from six, and both products are monic. -/
@[expose]
def ClassPolynomialSpec : Prop :=
  D.numeratorPolynomial.Monic ∧ D.denominatorPolynomial.Monic

/-- The actual products indexed by the four oriented class sets satisfy the
class-polynomial arithmetic specification. -/
theorem classPolynomialSpec : D.ClassPolynomialSpec :=
  ⟨D.numeratorPolynomial_monic, D.denominatorPolynomial_monic⟩

/-- Reduction modulo a good prime preserves the exact numerator degree. -/
theorem reduceNumerator_natDegree
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (D.integralPolynomials.reduceNumerator h6).natDegree = 2 * h := by
  calc
    (D.integralPolynomials.reduceNumerator h6).natDegree =
        (D.numeratorPolynomial.map (awaySixReduction ℓ h6)).natDegree := rfl
    _ = D.numeratorPolynomial.natDegree :=
      D.numeratorPolynomial_monic.natDegree_map _
    _ = 2 * h := D.numeratorPolynomial_natDegree

/-- Reduction modulo a good prime preserves the exact denominator degree. -/
theorem reduceDenominator_natDegree
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (D.integralPolynomials.reduceDenominator h6).natDegree = 2 * h := by
  calc
    (D.integralPolynomials.reduceDenominator h6).natDegree =
        (D.denominatorPolynomial.map (awaySixReduction ℓ h6)).natDegree := rfl
    _ = D.denominatorPolynomial.natDegree :=
      D.denominatorPolynomial_monic.natDegree_map _
    _ = 2 * h := D.denominatorPolynomial_natDegree

/-- The reduced numerator and denominator retain the common degree `2h`.
This is an internal consequence of monicity and coefficientwise reduction;
no geometric assertion is hidden in the statement. -/
theorem reducedClassPolynomials_degrees
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (D.reducedClassPolynomials h6).1.natDegree = 2 * h ∧
      (D.reducedClassPolynomials h6).2.natDegree = 2 * h :=
  ⟨D.reduceNumerator_natDegree h6, D.reduceDenominator_natDegree h6⟩

/-- A geometric root of the actual reduced numerator is the reduction of a
coordinate from orientation `1` or `11`. -/
theorem aeval_reducedNumerator_eq_zero_iff
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    {L : Type*} [CommRing L] [IsDomain L] [Algebra (ZMod ℓ) L]
    (x : L) :
    aeval x (D.reducedClassPolynomials h6).1 = 0 ↔
      (∃ i : D.orientation1.Index,
        x = algebraMap (ZMod ℓ) L
          (awaySixReduction ℓ h6
            (D.coordinate1 (D.orientation1.classes i)))) ∨
      (∃ i : D.orientation11.Index,
        x = algebraMap (ZMod ℓ) L
          (awaySixReduction ℓ h6
            (D.coordinate11 (D.orientation11.classes i)))) := by
  have hmap1 :
      (classPolynomial (fun i : D.orientation1.Index =>
        D.coordinate1 (D.orientation1.classes i))).map
          (awaySixReduction ℓ h6) =
        classPolynomial (fun i : D.orientation1.Index =>
          awaySixReduction ℓ h6
            (D.coordinate1 (D.orientation1.classes i))) := by
    classical
    unfold classPolynomial
    change (Polynomial.mapRingHom (awaySixReduction ℓ h6))
        (∏ i, (X - C (D.coordinate1 (D.orientation1.classes i)))) =
      ∏ i, (X - C (awaySixReduction ℓ h6
        (D.coordinate1 (D.orientation1.classes i))))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hmap11 :
      (classPolynomial (fun i : D.orientation11.Index =>
        D.coordinate11 (D.orientation11.classes i))).map
          (awaySixReduction ℓ h6) =
        classPolynomial (fun i : D.orientation11.Index =>
          awaySixReduction ℓ h6
            (D.coordinate11 (D.orientation11.classes i))) := by
    classical
    unfold classPolynomial
    change (Polynomial.mapRingHom (awaySixReduction ℓ h6))
        (∏ i, (X - C (D.coordinate11 (D.orientation11.classes i)))) =
      ∏ i, (X - C (awaySixReduction ℓ h6
        (D.coordinate11 (D.orientation11.classes i))))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  change aeval x (D.numeratorPolynomial.map (awaySixReduction ℓ h6)) = 0 ↔ _
  rw [numeratorPolynomial, classPolyA, Polynomial.map_mul, hmap1, hmap11]
  exact
    (aeval_classPolyA_eq_zero_iff
      (fun i : D.orientation1.Index =>
        awaySixReduction ℓ h6
          (D.coordinate1 (D.orientation1.classes i)))
      (fun i : D.orientation11.Index =>
        awaySixReduction ℓ h6
          (D.coordinate11 (D.orientation11.classes i))) x)

/-- A geometric root of the actual reduced denominator is the reduction of a
coordinate from orientation `5` or `7`. -/
theorem aeval_reducedDenominator_eq_zero_iff
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    {L : Type*} [CommRing L] [IsDomain L] [Algebra (ZMod ℓ) L]
    (x : L) :
    aeval x (D.reducedClassPolynomials h6).2 = 0 ↔
      (∃ i : D.orientation5.Index,
        x = algebraMap (ZMod ℓ) L
          (awaySixReduction ℓ h6
            (D.coordinate5 (D.orientation5.classes i)))) ∨
      (∃ i : D.orientation7.Index,
        x = algebraMap (ZMod ℓ) L
          (awaySixReduction ℓ h6
            (D.coordinate7 (D.orientation7.classes i)))) := by
  have hmap5 :
      (classPolynomial (fun i : D.orientation5.Index =>
        D.coordinate5 (D.orientation5.classes i))).map
          (awaySixReduction ℓ h6) =
        classPolynomial (fun i : D.orientation5.Index =>
          awaySixReduction ℓ h6
            (D.coordinate5 (D.orientation5.classes i))) := by
    classical
    unfold classPolynomial
    change (Polynomial.mapRingHom (awaySixReduction ℓ h6))
        (∏ i, (X - C (D.coordinate5 (D.orientation5.classes i)))) =
      ∏ i, (X - C (awaySixReduction ℓ h6
        (D.coordinate5 (D.orientation5.classes i))))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hmap7 :
      (classPolynomial (fun i : D.orientation7.Index =>
        D.coordinate7 (D.orientation7.classes i))).map
          (awaySixReduction ℓ h6) =
        classPolynomial (fun i : D.orientation7.Index =>
          awaySixReduction ℓ h6
            (D.coordinate7 (D.orientation7.classes i))) := by
    classical
    unfold classPolynomial
    change (Polynomial.mapRingHom (awaySixReduction ℓ h6))
        (∏ i, (X - C (D.coordinate7 (D.orientation7.classes i)))) =
      ∏ i, (X - C (awaySixReduction ℓ h6
        (D.coordinate7 (D.orientation7.classes i))))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  change aeval x (D.denominatorPolynomial.map (awaySixReduction ℓ h6)) = 0 ↔ _
  rw [denominatorPolynomial, classPolyB, Polynomial.map_mul, hmap5, hmap7]
  exact
    (aeval_classPolyB_eq_zero_iff
      (fun i : D.orientation5.Index =>
        awaySixReduction ℓ h6
          (D.coordinate5 (D.orientation5.classes i)))
      (fun i : D.orientation7.Index =>
        awaySixReduction ℓ h6
          (D.coordinate7 (D.orientation7.classes i))) x)

/-- A concrete factor index in the numerator (`r=1` or `r=11`). -/
abbrev NumeratorFactorIndex :=
  D.orientation1.Index ⊕ D.orientation11.Index

/-- A concrete factor index in the denominator (`r=5` or `r=7`). -/
abbrev DenominatorFactorIndex :=
  D.orientation5.Index ⊕ D.orientation7.Index

/-- The reduced coordinate belonging to a numerator factor. -/
@[expose]
def reducedNumeratorCoordinate
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    D.NumeratorFactorIndex → ZMod ℓ
  | .inl i => awaySixReduction ℓ h6
      (D.coordinate1 (D.orientation1.classes i))
  | .inr i => awaySixReduction ℓ h6
      (D.coordinate11 (D.orientation11.classes i))

/-- The reduced coordinate belonging to a denominator factor. -/
@[expose]
def reducedDenominatorCoordinate
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    D.DenominatorFactorIndex → ZMod ℓ
  | .inl i => awaySixReduction ℓ h6
      (D.coordinate5 (D.orientation5.classes i))
  | .inr i => awaySixReduction ℓ h6
      (D.coordinate7 (D.orientation7.classes i))

/-- Faithful algebraic content of I18: a common geometric root of the two
actual reduced root products produces one numerator factor and one
denominator factor whose reduced coordinates agree in the same extension
field.  No geometric point, reduction, or CM action is inserted here. -/
theorem common_root_gives_opposite_oriented_coordinates
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    {L : Type*} [CommRing L] [IsDomain L] [Algebra (ZMod ℓ) L]
    (x : L)
    (hA : aeval x (D.reducedClassPolynomials h6).1 = 0)
    (hB : aeval x (D.reducedClassPolynomials h6).2 = 0) :
    ∃ i : D.NumeratorFactorIndex, ∃ j : D.DenominatorFactorIndex,
      algebraMap (ZMod ℓ) L (D.reducedNumeratorCoordinate h6 i) =
        algebraMap (ZMod ℓ) L (D.reducedDenominatorCoordinate h6 j) := by
  rw [D.aeval_reducedNumerator_eq_zero_iff h6 x] at hA
  rw [D.aeval_reducedDenominator_eq_zero_iff h6 x] at hB
  rcases hA with ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    rcases hB with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨.inl i, .inl j, by
      simpa [reducedNumeratorCoordinate, reducedDenominatorCoordinate]
        using hi.symm.trans hj⟩
  · exact ⟨.inl i, .inr j, by
      simpa [reducedNumeratorCoordinate, reducedDenominatorCoordinate]
        using hi.symm.trans hj⟩
  · exact ⟨.inr i, .inl j, by
      simpa [reducedNumeratorCoordinate, reducedDenominatorCoordinate]
        using hi.symm.trans hj⟩
  · exact ⟨.inr i, .inr j, by
      simpa [reducedNumeratorCoordinate, reducedDenominatorCoordinate]
        using hi.symm.trans hj⟩

/-- Once geometric separation has supplied coprimality, the Wronskian of the
two *actual reduced class polynomials* is nonzero.  Monicity and the exact
degree are discharged from the root-product construction here. -/
theorem reducedClassPolynomials_wronskian_ne_zero
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    (hcop : IsCoprime (D.reducedClassPolynomials h6).1
      (D.reducedClassPolynomials h6).2)
    (hdegree_pos : 0 < 2 * h) (hdegree_lt : 2 * h < ℓ) :
    wronskianObstruction (D.reducedClassPolynomials h6).1
      (D.reducedClassPolynomials h6).2 ≠ 0 := by
  apply wronskianObstruction_ne_zero_zmod
      (Fact.out : ℓ.Prime) hcop
      (D.integralPolynomials.reduceNumerator_monic h6)
  · rw [(D.reducedClassPolynomials_degrees h6).1]
    exact hdegree_pos
  · rw [(D.reducedClassPolynomials_degrees h6).1]
    exact hdegree_lt

end OrientedCMIntegralCoordinates

end

end SptCM
