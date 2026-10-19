import blessed.SptCM.CM.ActualClassPolynomials
import blessed.SptCM.CM.Repaired.ActualCMValues
import Mathlib.Algebra.Polynomial.Eval.Subring
import blessed.SptCM.CM.Repaired.GaloisPolynomialDescent
import blessed.SptCM.CM.Repaired.AwaySixAlgebra

/-!
# Algebraic descent steps for the oriented CM class polynomials

This file builds the sound I16 descent chain from the actual analytic CM
values.  Individual CM values remain algebraic; only the Galois-stable root
product coefficients are descended to `ℤ[1/6]`.  The exact class-field
reciprocity and good integral-model evaluation laws remain explicit inputs.
-/

namespace SptCM.CM.Repaired

noncomputable section

open Polynomial

/-- A coefficientwise automorphism permuting a finite root family fixes its
root polynomial.  This is the exact algebraic descent calculation used after
CM reciprocity supplies the permutation. -/
theorem classPolynomial_map_of_permutation
    {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} [Fintype ι] (σ : R →+* R) (x : ι → R) (e : ι ≃ ι)
    (hσ : ∀ i, σ (x i) = x (e i)) :
    (classPolynomial x).map σ = classPolynomial x := by
  classical
  unfold classPolynomial
  change (Polynomial.mapRingHom σ) (∏ i, (X - C (x i))) =
    ∏ i, (X - C (x i))
  rw [map_prod]
  exact Fintype.prod_equiv e
    (fun i => (X - C (x i)).map σ)
    (fun i => X - C (x i)) (fun i => by simp [hσ i])

/-! ## Actual analytic root products and generic CM reciprocity -/

/-- The four actual finite oriented-class sets together with their CM points.
The coordinates are not fields: below they are defined by evaluating the
actual Dedekind-eta Hauptmodul at these points. -/
structure ActualOrientedCMCoordinates (n h : ℕ) where
  orientation1 : OrientedCMEnumeration n 1 h
  orientation11 : OrientedCMEnumeration n 11 h
  orientation5 : OrientedCMEnumeration n 5 h
  orientation7 : OrientedCMEnumeration n 7 h
  n_pos : 0 < n
  invariant1 : RawCMValueInvariant (n := n) (r := 1) analyticHauptmodul
  invariant11 : RawCMValueInvariant (n := n) (r := 11) analyticHauptmodul
  invariant5 : RawCMValueInvariant (n := n) (r := 5) analyticHauptmodul
  invariant7 : RawCMValueInvariant (n := n) (r := 7) analyticHauptmodul

/-- The canonical embedding `ℤ[1/6] → ℂ` is injective. -/
theorem awaySixToComplex_injective : Function.Injective awaySixToComplex := by
  unfold awaySixToComplex Localization.awayLift IsLocalization.Away.lift
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    have hz := congrArg awaySixToComplex h
    simpa [awaySixToComplex] using hz
  · intro h
    have hxy : x = y := Int.cast_injective h
    subst y
    rfl

/-- Sound I16 output: polynomials over `ℤ[1/6]` whose complex images are
literally the two actual analytic root products.  In particular this contains
no claim that an individual algebraic CM value lies in `ℤ[1/6]`. -/
structure ActualClassPolynomialSpec {n h : ℕ}
    (C : ActualOrientedCMCoordinates n h) where
  A : AwaySix[X]
  B : AwaySix[X]
  mapA : A.map awaySixToComplex =
    classPolynomial (fun i : C.orientation1.Index ⊕ C.orientation11.Index =>
      match i with
      | .inl j => actualOrientedHauptmodulValue C.invariant1 C.n_pos
          (C.orientation1.classes j)
      | .inr j => actualOrientedHauptmodulValue C.invariant11 C.n_pos
          (C.orientation11.classes j))
  mapB : B.map awaySixToComplex =
    classPolynomial (fun i : C.orientation5.Index ⊕ C.orientation7.Index =>
      match i with
      | .inl j => actualOrientedHauptmodulValue C.invariant5 C.n_pos
          (C.orientation5.classes j)
      | .inr j => actualOrientedHauptmodulValue C.invariant7 C.n_pos
          (C.orientation7.classes j))
  monicA : A.Monic
  monicB : B.Monic

namespace ActualOrientedCMCoordinates

variable {n h : ℕ} (C : ActualOrientedCMCoordinates n h)

/-- The actual analytic Hauptmodul roots in numerator orientations. -/
def numeratorRoot : C.orientation1.Index ⊕ C.orientation11.Index → ℂ
  | .inl i => actualOrientedHauptmodulValue C.invariant1 C.n_pos (C.orientation1.classes i)
  | .inr i => actualOrientedHauptmodulValue C.invariant11 C.n_pos (C.orientation11.classes i)

/-- The actual analytic Hauptmodul roots in denominator orientations. -/
def denominatorRoot : C.orientation5.Index ⊕ C.orientation7.Index → ℂ
  | .inl i => actualOrientedHauptmodulValue C.invariant5 C.n_pos (C.orientation5.classes i)
  | .inr i => actualOrientedHauptmodulValue C.invariant7 C.n_pos (C.orientation7.classes i)

/-- The honest complex root product over orientations `1` and `11`. -/
def actualNumeratorPolynomial : ℂ[X] := classPolynomial C.numeratorRoot

/-- The honest complex root product over orientations `5` and `7`. -/
def actualDenominatorPolynomial : ℂ[X] := classPolynomial C.denominatorRoot

/-- The actual analytic root products are monic, before any descent or
integrality input. -/
theorem actual_class_polynomials_monic :
    C.actualNumeratorPolynomial.Monic ∧ C.actualDenominatorPolynomial.Monic :=
  ⟨classPolynomial_monic _, classPolynomial_monic _⟩

/-- Their two degrees are the required `2h`, using only the four actual
oriented-class enumerations. -/
theorem actual_class_polynomials_natDegree :
    C.actualNumeratorPolynomial.natDegree = 2 * h ∧
      C.actualDenominatorPolynomial.natDegree = 2 * h := by
  constructor <;> simp [actualNumeratorPolynomial, actualDenominatorPolynomial,
    classPolynomial_natDegree, Fintype.card_sum, C.orientation1.card_eq,
    C.orientation11.card_eq, C.orientation5.card_eq, C.orientation7.card_eq, two_mul]



/-- A finite Galois class field containing all actual CM values.  The only CM
input is the standard reciprocity action on these algebraic values; rational
coefficient descent is proved below by Mathlib's Galois fixed-field theorem. -/
structure FiniteGaloisRealization
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] where
  embedding : L →ₐ[ℚ] ℂ
  embedding_injective : Function.Injective embedding
  numeratorAlgebraicRoot :
    C.orientation1.Index ⊕ C.orientation11.Index → L
  denominatorAlgebraicRoot :
    C.orientation5.Index ⊕ C.orientation7.Index → L
  realizesNumerator : ∀ i,
    embedding (numeratorAlgebraicRoot i) = C.numeratorRoot i
  realizesDenominator : ∀ i,
    embedding (denominatorAlgebraicRoot i) = C.denominatorRoot i
  numeratorPermutation : ∀ _σ : L ≃ₐ[ℚ] L,
    C.orientation1.Index ⊕ C.orientation11.Index ≃
      C.orientation1.Index ⊕ C.orientation11.Index
  denominatorPermutation : ∀ _σ : L ≃ₐ[ℚ] L,
    C.orientation5.Index ⊕ C.orientation7.Index ≃
      C.orientation5.Index ⊕ C.orientation7.Index
  numerator_reciprocity : ∀ (σ : L ≃ₐ[ℚ] L) i,
    σ (numeratorAlgebraicRoot i) =
      numeratorAlgebraicRoot (numeratorPermutation σ i)
  denominator_reciprocity : ∀ (σ : L ≃ₐ[ℚ] L) i,
    σ (denominatorAlgebraicRoot i) =
      denominatorAlgebraicRoot (denominatorPermutation σ i)

/-- The good-reduction refinement of a finite-Galois realization: every
algebraic CM representative is integral over `ℤ[1/6]`.  Notice that this says
that the roots lie in the integral closure inside `L`, not that they
themselves lie in `ℤ[1/6]`. -/
structure IntegralFiniteGaloisRealization
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    extends C.FiniteGaloisRealization L where
  integralNumerator : ∀ i,
    IsIntegral AwaySix (toFiniteGaloisRealization.numeratorAlgebraicRoot i)
  integralDenominator : ∀ i,
    IsIntegral AwaySix (toFiniteGaloisRealization.denominatorAlgebraicRoot i)

/-- Specialize the central E8 finite-Galois reciprocity boundary to
the two actual oriented Hauptmodul root families. -/
def FiniteGaloisRealization.ofE8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisCMReciprocity
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    C.FiniteGaloisRealization L where
  embedding := E.embedding
  embedding_injective := E.embedding_injective
  numeratorAlgebraicRoot := E.algebraicX
  denominatorAlgebraicRoot := E.algebraicY
  realizesNumerator := E.realizesX
  realizesDenominator := E.realizesY
  numeratorPermutation := E.permutationX
  denominatorPermutation := E.permutationY
  numerator_reciprocity := E.reciprocityX
  denominator_reciprocity := E.reciprocityY

/-- Specialize the integral E8 reciprocity/good-reduction boundary to the two
actual oriented Hauptmodul root families. -/
def IntegralFiniteGaloisRealization.ofE8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisIntegralCMReciprocity
      AwaySix
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    C.IntegralFiniteGaloisRealization L where
  toFiniteGaloisRealization := FiniteGaloisRealization.ofE8 C
    E.toE8FiniteGaloisCMReciprocity
  integralNumerator := E.integralX
  integralDenominator := E.integralY

namespace FiniteGaloisRealization

variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
  [IsGalois ℚ L] (F : C.FiniteGaloisRealization L)

/-- The numerator root product in a finite Galois CM class field. -/
def numeratorPolynomial : L[X] := classPolynomial F.numeratorAlgebraicRoot

/-- The denominator root product in the same class field. -/
def denominatorPolynomial : L[X] := classPolynomial F.denominatorAlgebraicRoot

/-- CM reciprocity fixes the class-field numerator polynomial. -/
theorem numeratorPolynomial_fixed (σ : L ≃ₐ[ℚ] L) :
    F.numeratorPolynomial.map σ.toRingHom = F.numeratorPolynomial :=
  classPolynomial_map_of_permutation σ.toRingHom
    F.numeratorAlgebraicRoot (F.numeratorPermutation σ)
    (F.numerator_reciprocity σ)

/-- CM reciprocity fixes the class-field denominator polynomial. -/
theorem denominatorPolynomial_fixed (σ : L ≃ₐ[ℚ] L) :
    F.denominatorPolynomial.map σ.toRingHom = F.denominatorPolynomial :=
  classPolynomial_map_of_permutation σ.toRingHom
    F.denominatorAlgebraicRoot (F.denominatorPermutation σ)
    (F.denominator_reciprocity σ)

/-- Mathlib's finite-Galois fixed-field theorem descends the numerator to
`ℚ[X]`; no fixed-field principle is assumed. -/
theorem exists_rational_numerator :
    ∃ A : ℚ[X], A.map (algebraMap ℚ L) = F.numeratorPolynomial :=
  exists_basePolynomial_of_galois_fixed F.numeratorPolynomial
    (numeratorPolynomial_fixed C F)

/-- The identical finite-Galois descent for the denominator. -/
theorem exists_rational_denominator :
    ∃ B : ℚ[X], B.map (algebraMap ℚ L) = F.denominatorPolynomial :=
  exists_basePolynomial_of_galois_fixed F.denominatorPolynomial
    (denominatorPolynomial_fixed C F)

/-- Embedding the class-field numerator product into `ℂ` gives literally the
actual analytic root product. -/
theorem map_numerator_eq_actual :
    F.numeratorPolynomial.map F.embedding.toRingHom =
      C.actualNumeratorPolynomial := by
  classical
  unfold numeratorPolynomial actualNumeratorPolynomial classPolynomial
  change (Polynomial.mapRingHom F.embedding.toRingHom)
      (∏ i, (X - Polynomial.C (F.numeratorAlgebraicRoot i))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [F.realizesNumerator]

/-- Embedding the class-field denominator product gives the actual analytic
root product. -/
theorem map_denominator_eq_actual :
    F.denominatorPolynomial.map F.embedding.toRingHom =
      C.actualDenominatorPolynomial := by
  classical
  unfold denominatorPolynomial actualDenominatorPolynomial classPolynomial
  change (Polynomial.mapRingHom F.embedding.toRingHom)
      (∏ i, (X - Polynomial.C (F.denominatorAlgebraicRoot i))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [F.realizesDenominator]

/-- The actual analytic root products therefore have rational coefficients,
derived from a finite Galois class field and its reciprocity action. -/
theorem actual_class_polynomials_rational_of_finiteGalois
    (F : C.FiniteGaloisRealization L) :
    (∃ A : ℚ[X], A.map (Rat.castHom ℂ) = C.actualNumeratorPolynomial) ∧
      ∃ B : ℚ[X], B.map (Rat.castHom ℂ) =
        C.actualDenominatorPolynomial := by
  obtain ⟨A, hA⟩ := exists_rational_numerator C F
  obtain ⟨B, hB⟩ := exists_rational_denominator C F
  refine ⟨⟨A, ?_⟩, ⟨B, ?_⟩⟩
  · rw [← map_numerator_eq_actual C F, ← hA, Polynomial.map_map]
    congr 1
    ext q
    simp
  · rw [← map_denominator_eq_actual C F, ← hB, Polynomial.map_map]
    congr 1
    ext q
    simp

end FiniteGaloisRealization

namespace IntegralFiniteGaloisRealization

variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
  [IsGalois ℚ L]

/-- A finite product of linear factors with roots integral over a base ring
has integral coefficients.  The proof forms the same product inside the
integral closure and maps it back to the ambient ring. -/
theorem classPolynomial_coeff_isIntegral
    {A R ι : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Fintype ι] (x : ι → R) (hx : ∀ i, IsIntegral A (x i)) :
    ∀ k, IsIntegral A ((classPolynomial x).coeff k) := by
  classical
  let xI : ι → integralClosure A R := fun i => ⟨x i, hx i⟩
  have hmap :
      (classPolynomial xI).map (integralClosure A R).subtype =
        classPolynomial x := by
    unfold classPolynomial
    change (Polynomial.mapRingHom (integralClosure A R).subtype)
        (∏ i, (X - C (xI i))) = ∏ i, (X - C (x i))
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    change (X - C (xI i)).map (integralClosure A R).subtype = _
    ext k
    rw [coeff_map]
    change (↑((X - C (xI i)).coeff k) : R) =
      (X - C (x i)).coeff k
    rw [coeff_sub, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> rfl
  intro k
  have hk := congrArg (fun p : R[X] => p.coeff k) hmap
  rw [coeff_map] at hk
  rw [← hk]
  exact (classPolynomial xI).coeff k |>.property

/-- Good reduction makes every coefficient of the numerator root product
integral over `ℤ[1/6]`. -/
theorem numeratorPolynomial_coeff_integral
    (F : C.IntegralFiniteGaloisRealization L) :
    ∀ k, IsIntegral AwaySix
      (F.toFiniteGaloisRealization.numeratorPolynomial.coeff k) :=
  classPolynomial_coeff_isIntegral
    F.toFiniteGaloisRealization.numeratorAlgebraicRoot F.integralNumerator

/-- Good reduction makes every coefficient of the denominator root product
integral over `ℤ[1/6]`. -/
theorem denominatorPolynomial_coeff_integral
    (F : C.IntegralFiniteGaloisRealization L) :
    ∀ k, IsIntegral AwaySix
      (F.toFiniteGaloisRealization.denominatorPolynomial.coeff k) :=
  classPolynomial_coeff_isIntegral
    F.toFiniteGaloisRealization.denominatorAlgebraicRoot F.integralDenominator

/-- Finite-Galois reciprocity and good reduction construct the genuine class
polynomials over `ℤ[1/6]`.  Rationality comes from the Galois fixed-field
theorem, integrality from the integral closure, and their intersection from
`exists_integrallyClosedPolynomial_of_fractional_integral`. -/
noncomputable def actualClassPolynomialSpec
    (F : C.IntegralFiniteGaloisRealization L) :
    ActualClassPolynomialSpec C := by
  let G := F.toFiniteGaloisRealization
  have hAexists :=
    exists_integrallyClosedPolynomial_of_fractional_integral
      G.numeratorPolynomial (G.exists_rational_numerator)
      (F.numeratorPolynomial_coeff_integral)
  let A := Classical.choose hAexists
  have hA := Classical.choose_spec hAexists
  have hBexists :=
    exists_integrallyClosedPolynomial_of_fractional_integral
      G.denominatorPolynomial (G.exists_rational_denominator)
      (F.denominatorPolynomial_coeff_integral)
  let B := Classical.choose hBexists
  have hB := Classical.choose_spec hBexists
  have mapA : A.map awaySixToComplex = C.actualNumeratorPolynomial := by
    rw [← G.map_numerator_eq_actual, ← hA, Polynomial.map_map]
    congr 1
    ext a
    rw [awaySixToComplex_eq_algebraMap]
    exact (G.embedding.commutes (awaySixToRat a)).symm
  have mapB : B.map awaySixToComplex = C.actualDenominatorPolynomial := by
    rw [← G.map_denominator_eq_actual, ← hB, Polynomial.map_map]
    congr 1
    ext a
    rw [awaySixToComplex_eq_algebraMap]
    exact (G.embedding.commutes (awaySixToRat a)).symm
  exact
    { A := A
      B := B
      mapA := mapA
      mapB := mapB
      monicA := Polynomial.monic_of_injective awaySixToComplex_injective
        (mapA ▸ C.actual_class_polynomials_monic.1)
      monicB := Polynomial.monic_of_injective awaySixToComplex_injective
        (mapB ▸ C.actual_class_polynomials_monic.2) }

end IntegralFiniteGaloisRealization

/-- I16 rationality from the exact standard E8 class-field reciprocity datum
and Mathlib's finite-Galois fixed-field theorem. -/
theorem actual_class_polynomials_rational_of_E8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisCMReciprocity
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    (∃ A : ℚ[X], A.map (Rat.castHom ℂ) = C.actualNumeratorPolynomial) ∧
      ∃ B : ℚ[X], B.map (Rat.castHom ℂ) =
        C.actualDenominatorPolynomial :=
  FiniteGaloisRealization.actual_class_polynomials_rational_of_finiteGalois
    C (FiniteGaloisRealization.ofE8 C E)

/-- The integral E8 datum in particular supplies the reciprocity datum needed
for rational coefficient descent. -/
theorem actual_class_polynomials_rational_of_integral_E8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisIntegralCMReciprocity
      AwaySix
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    (∃ A : ℚ[X], A.map (Rat.castHom ℂ) = C.actualNumeratorPolynomial) ∧
      ∃ B : ℚ[X], B.map (Rat.castHom ℂ) =
        C.actualDenominatorPolynomial :=
  C.actual_class_polynomials_rational_of_E8
    E.toE8FiniteGaloisCMReciprocity

/-- Potential good reduction in the integral E8 datum says exactly that all
actual analytic CM values in the two root families are integral away from
six.  Integrality is transported from the class field through its specified
complex embedding. -/
theorem actual_cm_values_integral_awaySix_of_E8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisIntegralCMReciprocity
      AwaySix
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    (∀ i, IsIntegral AwaySix (C.numeratorRoot i)) ∧
      ∀ j, IsIntegral AwaySix (C.denominatorRoot j) := by
  have hcomm :
      (algebraMap AwaySix ℂ).comp (RingHom.id AwaySix) =
        E.embedding.toRingHom.comp (algebraMap AwaySix L) := by
    ext a
    exact (E.embedding.commutes (awaySixToRat a)).symm
  constructor
  · intro i
    have hi := IsIntegral.map_of_comp_eq (RingHom.id AwaySix)
      E.embedding.toRingHom hcomm (E.integralX i)
    change IsIntegral AwaySix (E.embedding (E.algebraicX i)) at hi
    rwa [E.realizesX i] at hi
  · intro j
    have hj := IsIntegral.map_of_comp_eq (RingHom.id AwaySix)
      E.embedding.toRingHom hcomm (E.integralY j)
    change IsIntegral AwaySix (E.embedding (E.algebraicY j)) at hj
    rwa [E.realizesY j] at hj

/-- The exact I16 assembly: standard finite-Galois CM reciprocity and
good-reduction integrality produce a descent specification for the two fixed
actual analytic root products. -/
theorem exists_actualClassPolynomialSpec_of_E8
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (E : SptCM.RolenLiterature.E8FiniteGaloisIntegralCMReciprocity
      AwaySix
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) L
      C.numeratorRoot C.denominatorRoot) :
    Nonempty (ActualClassPolynomialSpec C) :=
  ⟨(IntegralFiniteGaloisRealization.ofE8 C E).actualClassPolynomialSpec⟩

/-- Generic good-reduction/regular-coordinate data.  `goodPoint` expresses
extension of a CM point to the interior of a good integral model, while
`regular_value` is evaluation of a regular coordinate on such a point.  Thus
membership of a Hauptmodul value in `S` is derived, not stored for each root. -/
structure GoodReductionEvaluation (S : Subring ℂ) where
  goodPoint : UpperHalfPlane → Prop
  good1 : ∀ Q : RawOrientedForm n 1,
    goodPoint (rawCMUpperHalfPlane C.n_pos Q)
  good11 : ∀ Q : RawOrientedForm n 11,
    goodPoint (rawCMUpperHalfPlane C.n_pos Q)
  good5 : ∀ Q : RawOrientedForm n 5,
    goodPoint (rawCMUpperHalfPlane C.n_pos Q)
  good7 : ∀ Q : RawOrientedForm n 7,
    goodPoint (rawCMUpperHalfPlane C.n_pos Q)
  regular_value : ∀ τ, goodPoint τ → analyticHauptmodul τ ∈ S

/-- Specialize the central E8 good-reduction/regular-evaluation boundary to
the four actual raw CM-point families. -/
def GoodReductionEvaluation.ofE8
    (S : Subring ℂ)
    (E : SptCM.RolenLiterature.E8GoodReductionRegularEvaluation
      UpperHalfPlane analyticHauptmodul S)
    (hq1 : ∀ Q : RawOrientedForm n 1,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq11 : ∀ Q : RawOrientedForm n 11,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq5 : ∀ Q : RawOrientedForm n 5,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq7 : ∀ Q : RawOrientedForm n 7,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q)) :
    C.GoodReductionEvaluation S where
  goodPoint := E.GoodInteriorPoint
  good1 := fun Q => E.potentialGoodReduction _ (hq1 Q)
  good11 := fun Q => E.potentialGoodReduction _ (hq11 Q)
  good5 := fun Q => E.potentialGoodReduction _ (hq5 Q)
  good7 := fun Q => E.potentialGoodReduction _ (hq7 Q)
  regular_value := E.regularEvaluation

/-- Potential good reduction and regularity of the actual coordinate imply
integrality of every actual numerator root. -/
theorem numeratorRoot_mem_integralSubring
    (S : Subring ℂ) (G : C.GoodReductionEvaluation S) :
    ∀ i, C.numeratorRoot i ∈ S := by
  intro i
  rcases i with i | i
  · generalize hQ : C.orientation1.classes i = q
    induction q using Quotient.inductionOn with
    | _ Q =>
        simp only [numeratorRoot]
        rw [hQ]
        exact G.regular_value _ (G.good1 Q)
  · generalize hQ : C.orientation11.classes i = q
    induction q using Quotient.inductionOn with
    | _ Q =>
        simp only [numeratorRoot]
        rw [hQ]
        exact G.regular_value _ (G.good11 Q)

/-- The same good-reduction argument for every actual denominator root. -/
theorem denominatorRoot_mem_integralSubring
    (S : Subring ℂ) (G : C.GoodReductionEvaluation S) :
    ∀ i, C.denominatorRoot i ∈ S := by
  intro i
  rcases i with i | i
  · generalize hQ : C.orientation5.classes i = q
    induction q using Quotient.inductionOn with
    | _ Q =>
        simp only [denominatorRoot]
        rw [hQ]
        exact G.regular_value _ (G.good5 Q)
  · generalize hQ : C.orientation7.classes i = q
    induction q using Quotient.inductionOn with
    | _ Q =>
        simp only [denominatorRoot]
        rw [hQ]
        exact G.regular_value _ (G.good7 Q)

/-- Every actual CM root lies in the integral subring supplied by the
E8 good-reduction theorem and regularity of the actual coordinate. -/
theorem actual_cm_values_integral_of_E8
    (S : Subring ℂ)
    (E : SptCM.RolenLiterature.E8GoodReductionRegularEvaluation
      UpperHalfPlane analyticHauptmodul S)
    (hq1 : ∀ Q : RawOrientedForm n 1,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq11 : ∀ Q : RawOrientedForm n 11,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq5 : ∀ Q : RawOrientedForm n 5,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q))
    (hq7 : ∀ Q : RawOrientedForm n 7,
      E.Qualified (rawCMUpperHalfPlane C.n_pos Q)) :
    (∀ i, C.numeratorRoot i ∈ S) ∧
      ∀ j, C.denominatorRoot j ∈ S := by
  let G := GoodReductionEvaluation.ofE8 C S E hq1 hq11 hq5 hq7
  exact ⟨C.numeratorRoot_mem_integralSubring S G,
    C.denominatorRoot_mem_integralSubring S G⟩

/-- A finite root product has all coefficients in a subring when all its
roots do.  This is the algebraic step missing from the former, false attempt
to lift each individual CM value to `ℤ[1/6]`. -/
theorem classPolynomial_coeff_mem_subring
    {ι : Type*} [Fintype ι] (S : Subring ℂ) (x : ι → ℂ)
    (hx : ∀ i, x i ∈ S) :
    ∀ k, (classPolynomial x).coeff k ∈ S := by
  let xS : ι → S := fun i => ⟨x i, hx i⟩
  have hmap : (classPolynomial xS).map S.subtype = classPolynomial x := by
    classical
    unfold classPolynomial
    change (Polynomial.mapRingHom S.subtype) (∏ i, (X - C (xS i))) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp [xS]
  have hrange : classPolynomial x ∈
      (Polynomial.mapRingHom S.subtype).range := ⟨classPolynomial xS, hmap⟩
  intro k
  obtain ⟨z, hz⟩ := (Polynomial.mem_map_range S.subtype).mp hrange k
  rw [← hz]
  exact z.property

/-- Consequently good reduction makes every coefficient of both genuine
complex root products integral in the chosen common integral subring. -/
theorem actual_class_polynomial_coefficients_integral
    (S : Subring ℂ) (G : C.GoodReductionEvaluation S) :
    (∀ k, C.actualNumeratorPolynomial.coeff k ∈ S) ∧
      ∀ k, C.actualDenominatorPolynomial.coeff k ∈ S := by
  exact ⟨classPolynomial_coeff_mem_subring S C.numeratorRoot
      (C.numeratorRoot_mem_integralSubring S G),
    classPolynomial_coeff_mem_subring S C.denominatorRoot
      (C.denominatorRoot_mem_integralSubring S G)⟩


end ActualOrientedCMCoordinates

end

end SptCM.CM.Repaired
