module

public import blessed.SptCM.Literature.RolenLiterature
public import blessed.SptCM.Analytic.DualityPairing
public import blessed.SptCM.Analytic.Repaired.StokesConstantTerm
public import blessed.SptCM.Analytic.Repaired.VectorFourierData
public import Mathlib.Algebra.Polynomial.Eval.Defs

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Repaired pairing and Borcherds specialization

This file separates the general results E5 and E6 from the computations needed
for their application to Rolen's form.  In particular, neither a vanishing
pairing, a vanishing Weyl vector, nor the normalized product identity occurs as
a field of an application record.
-/

namespace SptCM.Analytic.Repaired

open SptCM.RolenLiterature
open Polynomial

/-! ## I10: vector-valued input -/

/-- The exact, concrete specification of the four-component input.  Its first
conjunct is the combined scalar/finite Weil-generator law, while its second
conjunct expands to the zero constant term and the complete integral principal
part.  There is no caller-chosen predicate or application record. -/
@[expose]
def VectorInputSpec {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (n : ℕ)
    (F : FourComponentInput Form) : Prop :=
  HasFourComponentWeilGeneratorLaw E F ∧
    HasFourComponentFourierData n F.vectorSeries

/-- I10: the fixed vector-valued form built from the actual
`H_(24k-1) = eta P_k(j)` satisfies the complete Borcherds-input
specification.  The proof combines the exact E4 scalar generator laws, the
verified finite Weil matrices, and the independently proved Fourier
normalization of that same input. -/
theorem auxiliaryHn_vectorInputSpec
    {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form)
    (k : ℕ) (hk : 0 < k) (a : ℤ) :
    VectorInputSpec E (24 * k - 1)
      (auxiliaryFourComponentInput E k a) := by
  exact ⟨auxiliaryHn_weil_generators E k a,
    auxiliaryFourComponentInput_fourierData E k hk a⟩

/-- The constant coefficient vanishes in every component of any exact vector
input specification. -/
theorem VectorInputSpec.zeroConstantTerm
    {Form : Type*} [SMul ℂ Form] {E : EtaJGeneratorBasis Form}
    {n : ℕ} {F : FourComponentInput Form}
    (h : VectorInputSpec E n F) : ∀ s, F.vectorSeries 0 s = 0 :=
  h.2.1

/-- The full integral principal-part formula carried by an exact vector input
specification. -/
theorem VectorInputSpec.integralPrincipalPart
    {Form : Type*} [SMul ℂ Form] {E : EtaJGeneratorBasis Form}
    {n : ℕ} {F : FourComponentInput Form}
    (h : VectorInputSpec E n F) :
    ∀ r : ℤ, r < 0 → ∀ s,
      F.vectorSeries r s =
        if r = -(n : ℤ) then chiTwelveResidue s else 0 :=
  h.2.2

/-! ## I11: Weyl-vector vanishing -/

/-- The paper-internal cusp-theta contraction.  This is the output of the four
Atkin--Lehner and component calculations; it identifies the E6 pairing with a
scalar multiple of the already-computed scalar pairing, but does not state a
Weyl-vector conclusion. -/
structure CuspThetaContraction
    {Input Theta Cusp : Type*}
    (W : WeylVectorModel Input Theta ℝ Cusp)
    (F : Input) (pairing : ℝ) where
  factor : Cusp → ℝ
  contraction : ∀ c,
    W.regularizedPairing F (W.cuspTheta c) = factor c * pairing

/-- I11.  E6, the four cusp-theta contractions, and I09 imply that every Weyl
vector vanishes. -/
theorem all_weylVectors_eq_zero
    {Input Theta Cusp : Type*}
    (W : WeylVectorModel Input Theta ℝ Cusp)
    (hE6 : E6BruinierSchwagenscheidt W)
    (F : Input) (hadmissible : W.admissibleInput F)
    (pairing : ℝ) (hpairing : pairing = 0)
    (C : CuspThetaContraction W F pairing)
    (hnormalization_zero : W.normalization 0 = 0) :
    ∀ c, W.weylVector F c = 0 := by
  intro c
  have hp : W.regularizedPairing F (W.cuspTheta c) = 0 := by
    calc
      W.regularizedPairing F (W.cuspTheta c) = C.factor c * pairing :=
        C.contraction c
      _ = 0 := (mul_eq_zero_of_right (C.factor c) hpairing)
  rw [hE6 F c hadmissible, hp, hnormalization_zero]

/-! ## I12: normalized Borcherds product -/

/-- A concrete E5 model whose product-expansion predicate is the displayed
quotient.  Choosing this model before applying E5 prevents an opaque expansion
predicate from being postulated to equal the desired quotient afterwards. -/
@[expose]
def quotientBorcherdsModel
    {Input Divisor Product : Type*} [Field Product]
    (admissible : Input → Prop) (lift : Input → Product)
    (divisor : Product → Divisor) (predictedDivisor : Input → Divisor)
    (unitary : Product → Prop) (numerator denominator : Input → Product) :
    BorcherdsLiftModel Input Product Divisor where
  admissibleInput := admissible
  lift := lift
  divisor := divisor
  predictedDivisor := predictedDivisor
  hasUnitaryCharacter := unitary
  hasProductExpansion := fun F g => g = numerator F / denominator F

/-- The non-literature calculations needed after E5: identification of the
signed Heegner divisor, conversion of zero Weyl vectors to zero cusp
exponents, divisor-zero rigidity, and the two leading-term normalizations.
None of these fields is the normalized product identity. -/
structure NormalizedProductApplication
    {Input Divisor Product K Scalar Cusp : Type*}
    [Field K] [Field Product] [Algebra K Product] [Zero Scalar]
    (B : BorcherdsLiftModel Input Product Divisor)
    (F : Input) (classDivisor : Divisor) (classQuotient : Product)
    (leadingValue : Product → K) (weylVector : Cusp → Scalar) where
  CuspExponentsVanish : Prop
  predictedDivisor_identification : B.predictedDivisor F = classDivisor
  cuspExponents_of_weylVanishing :
    (∀ c, weylVector c = 0) → CuspExponentsVanish
  divisorZeroRigidity :
    B.divisor (B.lift F) = classDivisor → CuspExponentsVanish →
      ∃ c : K, B.lift F = algebraMap K Product c * classQuotient
  leadingValue_smul : ∀ (c : K) (g : Product),
    leadingValue (algebraMap K Product c * g) = c * leadingValue g
  classQuotient_normalized : leadingValue classQuotient = 1
  lift_normalized : leadingValue (B.lift F) = 1

/-- Scalar normalization removes the constant left by divisor rigidity. -/
theorem normalized_eq_of_scalar_multiple
    {K Product : Type*} [Field K] [Field Product] [Algebra K Product]
    (leadingValue : Product → K) (classQuotient product : Product)
    (hscalar : ∃ c : K, product = algebraMap K Product c * classQuotient)
    (hsmul : ∀ (c : K) (g : Product),
      leadingValue (algebraMap K Product c * g) = c * leadingValue g)
    (hclass : leadingValue classQuotient = 1)
    (hproduct : leadingValue product = 1) :
    classQuotient = product := by
  rcases hscalar with ⟨c, hc⟩
  have hc_one : c = 1 := by
    have h := congrArg leadingValue hc
    rw [hsmul, hclass, hproduct, mul_one] at h
    exact h.symm
  subst c
  simpa using hc.symm

/-- I12.  The general E5 theorem supplies the lift divisor and its concrete
product expansion.  The internally verified divisor/cusp calculations and
rigidity identify the lift with the normalized class-polynomial quotient. -/
theorem normalized_borcherds_product_identity
    {Input Divisor Product K Scalar Cusp : Type*}
    [Field K] [Field Product] [Algebra K Product] [Zero Scalar]
    (B : BorcherdsLiftModel Input Product Divisor)
    (hE5 : E5BruinierOno B)
    (F : Input) (hadmissible : B.admissibleInput F)
    (classDivisor : Divisor) (classQuotient : Product)
    (leadingValue : Product → K) (weylVector : Cusp → Scalar)
    (A : NormalizedProductApplication B F classDivisor classQuotient
      leadingValue weylVector)
    (hweylVanishing : ∀ c, weylVector c = 0) :
    classQuotient = B.lift F ∧ B.hasProductExpansion F classQuotient := by
  have hgeneral := hE5 F hadmissible
  have hdivisor : B.divisor (B.lift F) = classDivisor := by
    rw [hgeneral.1, A.predictedDivisor_identification]
  have hcusp : A.CuspExponentsVanish :=
    A.cuspExponents_of_weylVanishing hweylVanishing
  have heq : classQuotient = B.lift F :=
    normalized_eq_of_scalar_multiple leadingValue classQuotient (B.lift F)
      (A.divisorZeroRigidity hdivisor hcusp) A.leadingValue_smul
      A.classQuotient_normalized A.lift_normalized
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hgeneral.2.2

/-- Concrete quotient form of I12. -/
theorem normalized_classQuotient_eq_eulerQuotient
    {Input Divisor Product K Scalar Cusp : Type*}
    [Field K] [Field Product] [Algebra K Product] [Zero Scalar]
    (admissible : Input → Prop) (lift : Input → Product)
    (divisor : Product → Divisor) (predictedDivisor : Input → Divisor)
    (unitary : Product → Prop) (numerator denominator : Input → Product)
    (hE5 : E5BruinierOno
      (quotientBorcherdsModel admissible lift divisor predictedDivisor
        unitary numerator denominator))
    (F : Input) (hadmissible : admissible F)
    (classDivisor : Divisor) (classQuotient : Product)
    (leadingValue : Product → K) (weylVector : Cusp → Scalar)
    (A : NormalizedProductApplication
      (quotientBorcherdsModel admissible lift divisor predictedDivisor
        unitary numerator denominator)
      F classDivisor classQuotient leadingValue weylVector)
    (hweylVanishing : ∀ c, weylVector c = 0) :
    classQuotient = numerator F / denominator F := by
  obtain ⟨_, hexp⟩ := normalized_borcherds_product_identity
    (quotientBorcherdsModel admissible lift divisor predictedDivisor
      unitary numerator denominator)
    hE5 F hadmissible classDivisor classQuotient leadingValue weylVector A
    hweylVanishing
  exact hexp

end SptCM.Analytic.Repaired
