module

public import blessed.SptCM.Repair.SignedExponent
public import blessed.SptCM.CM.Borcherds
public import Mathlib.RingTheory.PowerSeries.Inverse

public section

-- Keep the existing ring operations on ZMod; the generic group reconstruction
-- introduced in this Mathlib version creates an incompatible negation instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Canonical stabilized Euler products

A formal infinite product is defined coefficientwise from its finite
truncations.  This gives an actual `PowerSeries`, rather than postulating one,
and immediately supplies the stabilization predicate used by the Borcherds
interface.  For the signed exponents of the paper the index-zero exponent
vanishes, so both products have constant coefficient one and are units.
-/

namespace SptCM.Repair

open scoped PowerSeries

/-- The finite truncation of an Euler product with the indicated factor
indices and natural exponents. -/
@[expose]
noncomputable def eulerProductTruncation {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ) (N : ℕ) : PowerSeries R :=
  ∏ i ∈ Finset.range N,
    (1 - PowerSeries.X ^ index i) ^ exponent i

/-- The canonical coefficientwise Euler product: its coefficient in degree
`d` is read from the finite truncation through `d + 1`. -/
@[expose]
noncomputable def stabilizedEulerProduct {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ) : PowerSeries R :=
  PowerSeries.mk fun d =>
    PowerSeries.coeff d (eulerProductTruncation (R := R) index exponent (d + 2))

@[simp] theorem coeff_stabilizedEulerProduct {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ) (d : ℕ) :
    PowerSeries.coeff d (stabilizedEulerProduct (R := R) index exponent) =
      PowerSeries.coeff d (eulerProductTruncation (R := R) index exponent (d + 2)) := by
  simp [stabilizedEulerProduct]

/-- The canonical construction satisfies the coefficientwise stabilization
predicate used by the infinite-product Borcherds theorem. -/
theorem stabilizedEulerProduct_isStabilized {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ) :
    SptCM.IsStabilizedEulerProduct
      (stabilizedEulerProduct (R := R) index exponent) index exponent := by
  intro d
  exact coeff_stabilizedEulerProduct (R := R) index exponent d

/-- If every factor with index zero has exponent zero, every finite
truncation has constant coefficient one. -/
theorem coeff_zero_eulerProductTruncation {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ)
    (hzero : ∀ i, index i = 0 → exponent i = 0) (N : ℕ) :
    PowerSeries.coeff 0 (eulerProductTruncation (R := R) index exponent N) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [eulerProductTruncation]
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  by_cases hindex : index i = 0
  · simp [hzero i hindex]
  · simp [PowerSeries.constantCoeff_X, zero_pow hindex]

/-- Hence the canonical stabilized product has constant coefficient one. -/
theorem coeff_zero_stabilizedEulerProduct {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ)
    (hzero : ∀ i, index i = 0 → exponent i = 0) :
    PowerSeries.coeff 0 (stabilizedEulerProduct (R := R) index exponent) = 1 := by
  rw [coeff_stabilizedEulerProduct (R := R)]
  exact coeff_zero_eulerProductTruncation (R := R) index exponent hzero 2

/-- A canonical stabilized product with no nontrivial index-zero factor is a
unit, since its constant coefficient is one. -/
theorem isUnit_stabilizedEulerProduct {R : Type*} [CommRing R]
    (index exponent : ℕ → ℕ)
    (hzero : ∀ i, index i = 0 → exponent i = 0) :
    IsUnit (stabilizedEulerProduct (R := R) index exponent : PowerSeries R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_zero_stabilizedEulerProduct (R := R) index exponent hzero]
  exact isUnit_one

/-- The actual numerator Euler product attached to the signed coefficients
of `H`. -/
@[expose]
noncomputable def eulerProductPlus {R : Type*} [CommRing R] (H : ℤ → ℤ) : PowerSeries R :=
  stabilizedEulerProduct (R := R) id (positiveEulerExponent H)

/-- The actual denominator Euler product attached to the signed coefficients
of `H`. -/
@[expose]
noncomputable def eulerProductMinus {R : Type*} [CommRing R] (H : ℤ → ℤ) : PowerSeries R :=
  stabilizedEulerProduct (R := R) id (negativeEulerExponent H)

private theorem positiveEulerExponent_zero (H : ℤ → ℤ) :
    positiveEulerExponent H 0 = 0 := by
  simp [positiveEulerExponent, signedEulerExponent, SptCM.Analytic.chi12]

private theorem negativeEulerExponent_zero (H : ℤ → ℤ) :
    negativeEulerExponent H 0 = 0 := by
  simp [negativeEulerExponent, signedEulerExponent, SptCM.Analytic.chi12]

/-- Complete sound specification of the two constructed products.  Besides
coefficientwise stabilization it records their normalized unit constant
terms and the pointwise signed-exponent decomposition. -/
@[expose]
def EulerProductSpec {R : Type*} [CommRing R]
    (H : ℤ → ℤ) (Pplus Pminus : PowerSeries R) : Prop :=
  SptCM.IsStabilizedEulerProduct Pplus id (positiveEulerExponent H) ∧
  SptCM.IsStabilizedEulerProduct Pminus id (negativeEulerExponent H) ∧
  PowerSeries.coeff 0 Pplus = 1 ∧
  PowerSeries.coeff 0 Pminus = 1 ∧
  IsUnit Pplus ∧ IsUnit Pminus ∧
  ∀ m : ℕ,
    (positiveEulerExponent H m : ℤ) -
        (negativeEulerExponent H m : ℤ) = signedEulerExponent H m ∧
      (positiveEulerExponent H m = 0 ∨
        negativeEulerExponent H m = 0)

/-- The canonical positive and negative Euler products satisfy the full
specification; no existence assumption for an infinite product is needed. -/
theorem eulerProducts_spec {R : Type*} [CommRing R] (H : ℤ → ℤ) :
    EulerProductSpec H (eulerProductPlus H : PowerSeries R)
      (eulerProductMinus H : PowerSeries R) := by
  have hplus0 : ∀ i, id i = 0 → positiveEulerExponent H i = 0 := by
    intro i hi
    simp only [id_eq] at hi
    subst i
    exact positiveEulerExponent_zero H
  have hminus0 : ∀ i, id i = 0 → negativeEulerExponent H i = 0 := by
    intro i hi
    simp only [id_eq] at hi
    subst i
    exact negativeEulerExponent_zero H
  refine ⟨stabilizedEulerProduct_isStabilized (R := R) id (positiveEulerExponent H),
    stabilizedEulerProduct_isStabilized (R := R) id (negativeEulerExponent H),
    coeff_zero_stabilizedEulerProduct (R := R) id (positiveEulerExponent H) hplus0,
    coeff_zero_stabilizedEulerProduct (R := R) id (negativeEulerExponent H) hminus0,
    isUnit_stabilizedEulerProduct (R := R) id (positiveEulerExponent H) hplus0,
    isUnit_stabilizedEulerProduct (R := R) id (negativeEulerExponent H) hminus0, ?_⟩
  intro m
  exact ⟨positive_sub_negativeEulerExponent H m,
    positive_or_negativeEulerExponent_eq_zero H m⟩

/-- Coefficientwise reduction of the integral auxiliary form.  Keeping this
as a named object makes the passage from the characteristic-zero Borcherds
identity to the characteristic-`ℓ` Frobenius argument explicit. -/
@[expose]
def reducedAuxiliaryForm (ℓ : ℕ) (H : ℤ → ℤ) :
    SptCM.Analytic.HForm (ZMod ℓ) :=
  fun r => (H r : ZMod ℓ)

/-- I14 and the algebraic part of the zero-Wronskian argument, specialized to
the *constructed* Euler products.  The caller supplies only the two genuinely
earlier mathematical conclusions: square-coefficient vanishing (from the
grid/duality argument) and the normalized Borcherds quotient identity.

In particular, no caller can choose arbitrary numerator or denominator power
series, or separately postulate their stabilization, exponent decomposition,
one-sidedness, or nonvanishing.  All of those facts are derived from the
canonical products above. -/
theorem wronskian_zero_from_canonical_eulerProducts
    (ℓ n : ℕ) [Fact ℓ.Prime] (H : ℤ → ℤ)
    (hsquareVanish : ∀ m : ℕ, ¬ℓ ∣ m →
      SptCM.CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
        reducedAuxiliaryForm ℓ H ((m : ℤ) ^ 2) = 0)
    (t : PowerSeries (ZMod ℓ)) (A B : Polynomial (ZMod ℓ))
    (htrans : Transcendental (ZMod ℓ) t)
    (ht : PowerSeries.derivative (R := ZMod ℓ) t ≠ 0)
    (hB : Polynomial.aeval t B ≠ 0)
    (hquotient :
      Polynomial.aeval (t : LaurentSeries (ZMod ℓ)) A /
          Polynomial.aeval (t : LaurentSeries (ZMod ℓ)) B =
        ((eulerProductPlus H : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)) /
          ((eulerProductMinus H : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)))
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    SptCM.wronskianObstruction A B = 0 := by
  have hspec :=
    eulerProducts_spec (R := ZMod ℓ) H
  have hdiv : ∀ m : ℕ,
      ℓ ∣ m ∨
        (ℓ ∣ positiveEulerExponent H m ∧
          ℓ ∣ negativeEulerExponent H m) := by
    intro m
    by_cases hm : ℓ ∣ m
    · exact Or.inl hm
    · right
      have hH :
          (H ((m : ℤ) ^ 2) : ZMod ℓ) = 0 :=
        hsquareVanish m hm hcanonical hsquarefree hmod hinert
      have hdiff :
          (positiveEulerExponent H m : ZMod ℓ) -
              (negativeEulerExponent H m : ZMod ℓ) = 0 := by
        rw [positive_sub_negativeEulerExponent_zmod]
        simp [signedEulerExponent, hH]
      rcases positive_or_negativeEulerExponent_eq_zero H m with hp | hn
      · rw [hp] at hdiff ⊢
        constructor
        · exact dvd_zero ℓ
        · have hz : (negativeEulerExponent H m : ZMod ℓ) = 0 := by
            simpa using hdiff
          exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ
            (negativeEulerExponent H m)).mp hz
      · rw [hn] at hdiff ⊢
        constructor
        · have hz : (positiveEulerExponent H m : ZMod ℓ) = 0 := by
            simpa using hdiff
          exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ
            (positiveEulerExponent H m)).mp hz
        · exact dvd_zero ℓ
  have hnumerator :
      PowerSeries.derivative (R := ZMod ℓ)
          (eulerProductPlus H : PowerSeries (ZMod ℓ)) = 0 :=
    SptCM.stabilizedEulerProduct_derivative_eq_zero ℓ
      (eulerProductPlus H) id (positiveEulerExponent H)
      hspec.1 (fun m => (hdiv m).imp_right And.left)
  have hdenominator :
      PowerSeries.derivative (R := ZMod ℓ)
          (eulerProductMinus H : PowerSeries (ZMod ℓ)) = 0 :=
    SptCM.stabilizedEulerProduct_derivative_eq_zero ℓ
      (eulerProductMinus H) id (negativeEulerExponent H)
      hspec.2.1 (fun m => (hdiv m).imp_right And.right)
  have hcross :
      Polynomial.aeval t A * (eulerProductMinus H) =
        (eulerProductPlus H) * Polynomial.aeval t B :=
    SptCM.powerSeries_crossProduct_of_laurentSeries_quotient
      t (eulerProductPlus H) (eulerProductMinus H) A B hB
      hspec.2.2.2.2.2.1.ne_zero hquotient
  exact SptCM.wronskian_zero_of_borcherds_quotient
    (PowerSeries.derivative (R := ZMod ℓ)) t A B htrans ht
    (eulerProductPlus H) (eulerProductMinus H)
    hspec.2.2.2.2.2.1.ne_zero hcross hnumerator hdenominator

end SptCM.Repair
