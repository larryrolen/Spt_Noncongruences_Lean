module

public import blessed.SptCM.Definitions
public import blessed.SptCM.Literature.AhlgrenKimGrid
public import blessed.SptCM.Literature.SquarefreeCusps
public import blessed.SptCM.Analytic.PaperCoefficientModels
public import blessed.SptCM.Arithmetic.SmallDiscriminant
public import blessed.SptCM.CM.ClassPolynomials
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.FieldTheory.Galois.Basic

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# The literature boundary for the Rolen SPT argument

This file records precisely the eleven groups of *general* external results
allowed by the completion register.  It deliberately contains no construction
of Rolen's grid, auxiliary forms, class polynomials, specialized Borcherds
product, collision map, or final classification.  General results are
proposition-valued, while E4's published modular grid is deliberately stored
as exact data (fixed forms, qualification, principal parts, range, and
uniqueness) rather than collapsed to an opaque proposition.  The neutral
models only name the operations and predicates occurring in those theorems.
-/

namespace SptCM.RolenLiterature

/-! ## E1--E3: SPT congruences and harmonic Maass forms -/

/-- A congruence on one explicitly specified arithmetic progression. -/
@[expose]
def SptProgressionCongruence (modulus shift : ℕ) : Prop :=
  ∀ k : ℕ, modulus ∣ spt (modulus * k + shift)

/-- Andrews' modulus-five congruence. -/
@[expose]
def Andrews5 : Prop := SptProgressionCongruence 5 4

/-- Andrews' modulus-seven congruence. -/
@[expose]
def Andrews7 : Prop := SptProgressionCongruence 7 5

/-- Andrews' modulus-thirteen congruence. -/
@[expose]
def Andrews13 : Prop := SptProgressionCongruence 13 6

/-- E1 (Andrews): exactly the three published congruences, with the shifts
`4`, `5`, and `6` appearing in the source.  Primality and the computation of
the canonical inverse of `24` are deliberately not external assumptions. -/
@[expose]
def E1AndrewsCongruences : Prop :=
  Andrews5 ∧ Andrews7 ∧ Andrews13

/-- E2 (Ahlgren--Kim, Theorem 3): the exact finite-range exclusion used at
the final cutoff. -/
@[expose]
def E2AhlgrenKimFiniteExclusion : Prop :=
  ∀ ℓ : ℕ, CanonicalCongruencePrime ℓ → ℓ < 10 ^ 11 →
    ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13

/-- E2 (Ahlgren--Kim, Proposition 6): their normalized theta-cycle input,
only in the prime range in which it is cited. -/
@[expose]
def E2AhlgrenKimThetaCycle : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ →
    SptCM.Analytic.AhlgrenKimThetaCycleFromUInput ℓ

/-- The two independently cited parts of E2. -/
@[expose]
def E2AhlgrenKim : Prop :=
  E2AhlgrenKimFiniteExclusion ∧ E2AhlgrenKimThetaCycle

/-- Neutral operations in the general completion/shadow and Hecke theorem. -/
structure HarmonicMaassModel (Completion Series : Type*) where
  holomorphicPart : Completion → Series
  shadow : Completion → Series
  heckeThreeHalves : ℕ → Completion → Completion
  heckeOneHalf : ℕ → Series → Series
  shadowScale : ℕ → Series → Series

/-- E3 (Bringmann): existence of the completion with the published
holomorphic part and normalized eta shadow. -/
@[expose]
def BringmannCompletion {Completion Series : Type*}
    (M : HarmonicMaassModel Completion Series)
    (f eta : Series) (shadowNormalization : Series → Series) : Prop :=
  ∃ F : Completion,
    M.holomorphicPart F = f ∧ M.shadow F = shadowNormalization eta

/-- E3 (general harmonic-Maass-form theory): the dual-weight
Hecke/shadow intertwining identity, including its scalar normalization. -/
@[expose]
def HeckeShadowIntertwining {Completion Series : Type*}
    (M : HarmonicMaassModel Completion Series) : Prop :=
  ∀ (m : ℕ) (F : Completion),
    M.shadow (M.heckeThreeHalves m F) =
      M.shadowScale m (M.heckeOneHalf m (M.shadow F))

/-- Compatibility conjunction for older callers. -/
@[expose]
def E3CompletionAndHecke {Completion Series : Type*}
    (M : HarmonicMaassModel Completion Series)
    (f eta : Series) (shadowNormalization : Series → Series) : Prop :=
  BringmannCompletion M f eta shadowNormalization ∧
    HeckeShadowIntertwining M

/-! ## E4--E7: standard modular-form and Borcherds theory -/

/-- The separate general principles grouped as E4 in the register.  The
predicates are intentionally generic: an application still has to prove that
Rolen's concrete form satisfies their hypotheses. -/
structure StandardModularFormModel (Form : Type*) where
  isDedekindEta : Form → Prop
  isModularInvariant : Form → Prop
  isEisensteinSeries : Form → Prop
  isEtaJOrEisenstein : Form → Prop
  hasStandardTransformationLaw : Form → Prop
  nonvanishingOnUpperHalfPlane : Form → Prop
  hasIntegralUnitProductExpansion : Form → Prop
  isWeaklyHolomorphic : Form → Prop
  hasIntegralPrincipalPart : Form → Prop
  hasIntegralFourierExpansion : Form → Prop
  isWeightTwo : Form → Prop
  constantTerm : Form → ℂ
  heckeOperator : ℕ → Form → Form
  heckeLaw : ℕ → Form → Prop

/-- E4: Dedekind eta transformation, nonvanishing, and integral unit-product
expansion. -/
@[expose]
def DedekindEtaFoundations {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ F, M.isDedekindEta F →
    M.hasStandardTransformationLaw F ∧
      M.nonvanishingOnUpperHalfPlane F ∧
      M.hasIntegralUnitProductExpansion F

/-- E4: modularity and integral Fourier expansion of the modular invariant. -/
@[expose]
def ModularInvariantFoundations {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ F, M.isModularInvariant F →
    M.hasStandardTransformationLaw F ∧ M.hasIntegralFourierExpansion F

/-- E4: weights/transformation laws and integral expansions of the relevant
Eisenstein series. -/
@[expose]
def EisensteinFoundations {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ F, M.isEisensteinSeries F →
    M.hasStandardTransformationLaw F ∧ M.hasIntegralFourierExpansion F

/-- E4: principal-part integrality for qualified weakly holomorphic forms. -/
@[expose]
def PrincipalPartIntegrality {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ F, M.isWeaklyHolomorphic F → M.hasIntegralPrincipalPart F →
    M.hasIntegralFourierExpansion F

/-- E4: general modular Hecke laws, without a paper-specific identity. -/
@[expose]
def GeneralModularHeckeLaws {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ m F, M.isWeaklyHolomorphic F → M.heckeLaw m F

/-- E4: the weight-two residue/constant-term theorem. -/
@[expose]
def WeightTwoResidueTheorem {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  ∀ F, M.isWeaklyHolomorphic F → M.isWeightTwo F →
    M.constantTerm F = 0

/-- Compatibility conjunction for the proposition-valued general E4
foundations.  The published grid is intentionally not hidden in this
conjunction: its exact data-bearing theorem is stored separately in
`RolenLiterature.e4PublishedGrid`. -/
@[expose]
def E4StandardModularForms {Form : Type*}
    (M : StandardModularFormModel Form) : Prop :=
  DedekindEtaFoundations M ∧ ModularInvariantFoundations M ∧
    EisensteinFoundations M ∧ PrincipalPartIntegrality M ∧
    GeneralModularHeckeLaws M ∧ WeightTwoResidueTheorem M

/-- Neutral output of the general Bruinier--Ono lift. -/
structure BorcherdsLiftModel (Input Product Divisor : Type*) where
  admissibleInput : Input → Prop
  lift : Input → Product
  divisor : Product → Divisor
  predictedDivisor : Input → Divisor
  hasUnitaryCharacter : Product → Prop
  hasProductExpansion : Input → Product → Prop

/-- E5 (Bruinier--Ono, Theorem 6.1): the general lift theorem.  It says
nothing here about Rolen's particular input or normalized quotient. -/
@[expose]
def E5BruinierOno {Input Product Divisor : Type*}
    (M : BorcherdsLiftModel Input Product Divisor) : Prop :=
  ∀ F, M.admissibleInput F →
    M.divisor (M.lift F) = M.predictedDivisor F ∧
      M.hasUnitaryCharacter (M.lift F) ∧
      M.hasProductExpansion F (M.lift F)

/-- Neutral data in the general Weyl-vector formula. -/
structure WeylVectorModel (Input Theta Scalar Cusp : Type*) where
  admissibleInput : Input → Prop
  weylVector : Input → Cusp → Scalar
  regularizedPairing : Input → Theta → Scalar
  cuspTheta : Cusp → Theta
  normalization : Scalar → Scalar

/-- E6 (Bruinier--Schwagenscheidt, equation (11)): the Weyl vector at each
cusp is the normalized regularized theta pairing. -/
@[expose]
def E6BruinierSchwagenscheidt
    {Input Theta Scalar Cusp : Type*}
    (M : WeylVectorModel Input Theta Scalar Cusp) : Prop :=
  ∀ F c, M.admissibleInput F →
    M.weylVector F c =
      M.normalization (M.regularizedPairing F (M.cuspTheta c))

/-- General eta-quotient and integral modular-curve predicates used in E7. -/
structure LigozatModel (Exponent Quotient Cusp Order Curve : Type*) where
  ligozatConditions : Exponent → Prop
  quotient : Exponent → Quotient
  isModularFunction : Quotient → Prop
  cuspOrder : Quotient → Cusp → Order
  orderFormula : Exponent → Cusp → Order
  characterCriterion : Exponent → Prop
  hasTrivialCharacter : Quotient → Prop
  isLevelSixModularCurve : Curve → Prop
  isIntegralModelAwayFromLevel : Curve → Prop
  hasGenusZeroGeometricFibers : Curve → Prop
  hasDisjointStandardCuspSections : Curve → Prop

/-- E7: Ligozat's general modularity, character, and cusp-order theorem. -/
@[expose]
def LigozatEtaQuotients
    {Exponent Quotient Cusp Order Curve : Type*}
    (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  ∀ e, M.ligozatConditions e →
    M.isModularFunction (M.quotient e) ∧
    (∀ c, M.cuspOrder (M.quotient e) c = M.orderFormula e c) ∧
    (M.characterCriterion e → M.hasTrivialCharacter (M.quotient e))

/-- E7: good integral model of the compactified level-six modular curve away
from the level. -/
@[expose]
def X0SixGoodIntegralModel
    {Exponent Quotient Cusp Order Curve : Type*}
    (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  ∀ X : Curve, M.isLevelSixModularCurve X →
    M.isIntegralModelAwayFromLevel X

/-- E7: smooth irreducible genus-zero geometric fibers away from six. -/
@[expose]
def X0SixGenusZeroFibers
    {Exponent Quotient Cusp Order Curve : Type*}
    (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  ∀ X : Curve, M.isLevelSixModularCurve X →
    M.hasGenusZeroGeometricFibers X

/-- E7: disjointness of the four standard cusp sections away from six. -/
@[expose]
def X0SixDisjointCusps
    {Exponent Quotient Cusp Order Curve : Type*}
    (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  ∀ X : Curve, M.isLevelSixModularCurve X →
    M.hasDisjointStandardCuspSections X

/-- Compatibility conjunction for older callers. -/
@[expose]
def E7LigozatAndIntegralModel
    {Exponent Quotient Cusp Order Curve : Type*}
    (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  LigozatEtaQuotients M ∧ X0SixGoodIntegralModel M

/-! ### General integral degree-one geometry used with E7 -/

/-- Operations on rational functions on a proper integral curve.  This is a
neutral geometric model: it contains no eta quotient, CM point, Hauptmodul,
or paper-specific conclusion. -/
structure IntegralCurveFunctionGeometry
    (Function Divisor Curve Section Expansion : Type*) where
  divisor : Function → Divisor
  sectionDifference : Curve → Section → Section → Divisor
  hasNoInteriorZeroOrPole : Function → Curve → Prop
  hasIntegralUnitExpansionAt : Function → Section → Expansion → Prop
  hasNoVerticalComponent : Function → Curve → Prop
  identifiesWithProjectiveLine : Function → Curve → Prop

/-- General horizontal-divisor principle: on a smooth proper curve, a
rational function with no interior zero or pole and cusp orders `+1,-1`
has divisor the difference of those two cusp sections. -/
@[expose]
def E7HorizontalDivisorPrinciple
    {Function Divisor Curve Section Expansion Order : Type*}
    [Zero Order] [One Order] [Neg Order]
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Section Expansion)
    (isIntegralModel hasGenusZeroFibers : Curve → Prop)
    (isRationalFunction : Function → Prop)
    (cuspOrder : Function → Section → Order) : Prop :=
  ∀ X f zero infinity,
    isIntegralModel X →
    hasGenusZeroFibers X →
    isRationalFunction f →
    G.hasNoInteriorZeroOrPole f X →
    cuspOrder f zero = 1 →
    cuspOrder f infinity = -1 →
    (∀ c, c ≠ zero → c ≠ infinity → cuspOrder f c = 0) →
    G.divisor f = G.sectionDifference X zero infinity

/-- General integral spreading principle: an integral unit expansion at a
horizontal cusp excludes an additional vertical divisor component. -/
@[expose]
def E7NoVerticalComponentPrinciple
    {Function Divisor Curve Section Expansion : Type*}
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Section Expansion)
    (isIntegralModel hasDisjointStandardCuspSections : Curve → Prop) : Prop :=
  ∀ X f zero infinity expansion,
    isIntegralModel X →
    hasDisjointStandardCuspSections X →
    G.divisor f = G.sectionDifference X zero infinity →
    G.hasIntegralUnitExpansionAt f infinity expansion →
    G.hasNoVerticalComponent f X

/-- General degree-one divisor criterion on a smooth proper integral
genus-zero model. -/
@[expose]
def E7IntegralDegreeOneCriterion
    {Function Divisor Curve Section Expansion : Type*}
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Section Expansion)
    (isIntegralModel hasGenusZeroFibers
      hasDisjointStandardCuspSections : Curve → Prop) : Prop :=
  ∀ X f zero infinity,
    isIntegralModel X →
    hasGenusZeroFibers X →
    hasDisjointStandardCuspSections X →
    G.divisor f = G.sectionDifference X zero infinity →
    G.hasNoVerticalComponent f X →
    G.identifiesWithProjectiveLine f X

/-! ## E8--E9: general CM and quaternionic results -/

/-!
### Exact class-number content of E8

The propositions below pin the class-number part of E8.  They avoid the
uninterpreted `classCountCorrect` label in the older all-purpose reduction
model.  The external boundary supplies only the standard form/ideal-class
equivalences, including their fixed local orientations above `2` and `3`.
The four actions and every cardinality conclusion remain internal deductions.
-/

/-- The concrete finite type counted by `negativeClassNumber`. -/
abbrev ReducedFormClasses (n : ℕ) :=
  {i : ReducedFormIndex (Nat.sqrt (n / 3)) // IsReducedFormIndex n i}

/-- In the odd negative-discriminant case used here, `-n` is fundamental
exactly when `n` is squarefree and `n ≡ 3 (mod 4)`. -/
@[expose]
def IsNegativeFundamentalDiscriminant (n : ℕ) : Prop :=
  Squarefree n ∧ n % 4 = 3

/-- The canonical quadratic order
`ℤ[(1 + √(-n))/2] = ℤ[X]/(X²-X+(n+1)/4)` in the paper's range
`n ≡ 3 (mod 4)`.  Using this concrete quotient prevents substitution of an
unrelated domain with a conveniently chosen class number. -/
abbrev NegativeQuadraticOrder (n : ℕ) :=
  AdjoinRoot
    (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))

/-- Additional unproved E8 input: the specified negative quadratic order is a domain in the fundamental-discriminant range. No theorem-level source for the exact interface is certified. -/
@[expose]
def E8NegativeQuadraticOrderDomain (n : ℕ) : Prop :=
  IsNegativeFundamentalDiscriminant n →
    Nonempty (IsDomain (NegativeQuadraticOrder n))

/-- Additional unproved E8 input: reduced forms correspond to proper ideal classes with these boundary conventions. This exact correspondence has not been proved or matched to a cited theorem. -/
@[expose]
def E8ReducedFormClassification (n : ℕ)
    [IsDomain (NegativeQuadraticOrder n)] : Prop :=
  IsNegativeFundamentalDiscriminant n →
    Nonempty (ClassGroup (NegativeQuadraticOrder n) ≃ ReducedFormClasses n)

/-- The standard fixed-local-orientation refinement of the form/ideal-class
correspondence.  Choosing one prime above each of `2` and `3` gives four
possibilities, represented by the residues `1, 11, 5, 7` modulo `12`.
This datum contains neither an action nor a cardinality equation. -/
structure FourOrientedClassEquivalences (n : ℕ)
    [IsDomain (NegativeQuadraticOrder n)] where
  orientation1 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 1
  orientation11 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 11
  orientation5 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 5
  orientation7 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 7

/-- Additional unproved E8 input: the four concrete level-six oriented-form quotients are the four specified proper ideal-class torsors. Their exact equivalences require separate justification. -/
@[expose]
def E8FourOrientedFormClassification (n : ℕ)
    [IsDomain (NegativeQuadraticOrder n)] : Prop :=
  IsNegativeFundamentalDiscriminant n → n % 24 = 23 →
    Nonempty (FourOrientedClassEquivalences n)

/-- The displayed maps satisfy the group-action laws. -/
@[expose]
def IsIdealClassAction
    {R X : Type*} [CommRing R] [IsDomain R]
    (act : ClassGroup R → X → X) : Prop :=
  (∀ x, act 1 x = x) ∧
    (∀ g h x, act (g * h) x = act g (act h x))

/-- A concrete ideal-class action is simply transitive. -/
@[expose]
def IsSimplyTransitiveIdealClassAction
    {R X : Type*} [CommRing R] [IsDomain R]
    (act : ClassGroup R → X → X) : Prop :=
  Nonempty X ∧ ∀ x y, ∃! g : ClassGroup R, act g x = y

/-- Exact ideal-class-action output allowed by E8: action laws and simple
transitivity, but no cardinality conclusion. -/
@[expose]
def E8IdealClassAction
    {R X : Type*} [CommRing R] [IsDomain R]
    (act : ClassGroup R → X → X) : Prop :=
  IsIdealClassAction act ∧ IsSimplyTransitiveIdealClassAction act

/-- Neutral CM/class-field/reduction data. -/
structure CMTheoryModel (Order IdealClass CMPoint Reduction Endomorphism : Type*) where
  acts : IdealClass → CMPoint → CMPoint
  classCount : Order → ℕ
  pointsForOrder : Order → Set CMPoint
  actionSimplyTransitive : Order → Prop
  classCountCorrect : Order → Prop
  hasPotentiallyGoodReduction : CMPoint → Prop
  reduction : CMPoint → Reduction
  inertAt : ℕ → CMPoint → Prop
  supersingular : Reduction → Prop
  specializedAction : CMPoint → Endomorphism
  specializationInjective : CMPoint → Prop

/-- Additional unproved E8 application interface: the specified quadratic-order families specialize compatibly with conjugation and the level-six structure. No collision, noncommutation, volume or separation conclusion is assumed here. -/
structure E8OrientedQuadraticSpecialization
    (n : ℕ)
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (M : CMTheoryModel Order IdealClass CMPoint Reduction D) where
  point : ∀ r : ℕ, RawOrientedForm n r → CMPoint
  specialize :
    ∀ {r : ℕ}, RawOrientedForm n r → NegativeQuadraticOrder n →+* D
  specializedGenerator :
    ∀ {r : ℕ} (Q : RawOrientedForm n r),
      M.specializedAction (point r Q) =
        specialize Q (AdjoinRoot.root
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))
  conjugationGenerator :
    ∀ {r : ℕ} (Q : RawOrientedForm n r),
      star (specialize Q (AdjoinRoot.root
        (Polynomial.X ^ 2 - Polynomial.X +
          Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))) =
        1 - specialize Q (AdjoinRoot.root
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))
  levelOrder : Subring D
  levelAction : levelOrder →+* ZMod 6
  specializedGenerator_mem_levelOrder :
    ∀ {r : ℕ} (Q : RawOrientedForm n r),
      M.specializedAction (point r Q) ∈ levelOrder
  levelAction_specializedGenerator :
    ∀ {r : ℕ} (Q : RawOrientedForm n r),
      levelAction
          ⟨M.specializedAction (point r Q),
            specializedGenerator_mem_levelOrder Q⟩ =
        (((r + 1) / 2 : ℕ) : ZMod 6)

/-- E8: simply transitive proper ideal-class action at each fixed order and
orientation. -/
@[expose]
def CMClassAction
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  ∀ O, M.actionSimplyTransitive O

/-- E8: correctness of the general proper-ideal-class count. -/
@[expose]
def CMClassCount
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  ∀ O, M.classCountCorrect O


/-- Additional unproved E8 application datum: the actual analytic CM values have the specified finite Galois realization and permutation actions. No coefficients of root polynomials are asserted here. -/
structure E8FiniteGaloisCMReciprocity
    (I J L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (x : I → ℂ) (y : J → ℂ) where
  embedding : L →ₐ[ℚ] ℂ
  embedding_injective : Function.Injective embedding
  algebraicX : I → L
  algebraicY : J → L
  realizesX : ∀ i, embedding (algebraicX i) = x i
  realizesY : ∀ j, embedding (algebraicY j) = y j
  permutationX : ∀ _σ : L ≃ₐ[ℚ] L, I ≃ I
  permutationY : ∀ _σ : L ≃ₐ[ℚ] L, J ≃ J
  reciprocityX : ∀ (σ : L ≃ₐ[ℚ] L) i,
    σ (algebraicX i) = algebraicX (permutationX σ i)
  reciprocityY : ∀ (σ : L ≃ₐ[ℚ] L) j,
    σ (algebraicY j) = algebraicY (permutationY σ j)

/-- Additional unproved E8 integral refinement: each specified CM root is integral over the chosen coefficient ring. This exact realization is assumed, not derived from a certified literature theorem. -/
structure E8FiniteGaloisIntegralCMReciprocity
    (A I J L : Type*) [CommRing A] [Field L] [Algebra A L]
    [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (x : I → ℂ) (y : J → ℂ)
    extends E8FiniteGaloisCMReciprocity I J L x y where
  integralX : ∀ i, IsIntegral A (toE8FiniteGaloisCMReciprocity.algebraicX i)
  integralY : ∀ j, IsIntegral A (toE8FiniteGaloisCMReciprocity.algebraicY j)

/-- Source-facing existence statement for the class field of two specified
finite CM-value families.  It asserts only a finite Galois realization,
Shimura reciprocity on the roots, and their good-reduction integrality over
the chosen coefficient ring.  Polynomial descent is deliberately absent. -/
@[expose]
def E8IntegralCMClassFieldExistence
    (A I J : Type*) [CommRing A] (x : I → ℂ) (y : J → ℂ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra A L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Nonempty (E8FiniteGaloisIntegralCMReciprocity A I J L x y)

/-- General good-prime specialization of an integral CM class field.  The
residue homomorphism is required only to extend coefficientwise reduction;
there is no assertion here about polynomial roots, collisions, or equality
of specialized moduli points. -/
structure E8IntegralCMResidueSpecialization
    (A L k : Type*) (ℓ : ℕ) [CommRing A] [CommRing L] [Field k]
    [Algebra A L] [Algebra (ZMod ℓ) k]
    (coefficientReduction : A →+* ZMod ℓ) where
  residue : L →+* k
  compatible :
    residue.comp (algebraMap A L) =
      (algebraMap (ZMod ℓ) k).comp coefficientReduction

/-- General degree-one-coordinate realization of two specialized CM
families on a good fiber.  Equality of coordinate values determines equality
of the specialized level-structure points via the single global injectivity
law; no particular collision is asserted. -/
structure E8IntegralCoordinateSpecialization
    (I J k SpecialPoint : Type*) [Field k]
    (specializedX : I → k) (specializedY : J → k) where
  pointX : I → SpecialPoint
  pointY : J → SpecialPoint
  coordinate : SpecialPoint → k
  realizesX : ∀ i, coordinate (pointX i) = specializedX i
  realizesY : ∀ j, coordinate (pointY j) = specializedY j
  coordinate_injective : Function.Injective coordinate

/-- General potential-good-reduction plus regular-evaluation law.  A
qualified CM point first extends to a good interior point; a regular modular
coordinate evaluated there lies in the chosen integral subring.  Root or
polynomial integrality is not a field of this interface. -/
structure E8GoodReductionRegularEvaluation
    (Point : Type*) (value : Point → ℂ) (S : Subring ℂ) where
  Qualified : Point → Prop
  GoodInteriorPoint : Point → Prop
  potentialGoodReduction : ∀ P, Qualified P → GoodInteriorPoint P
  regularEvaluation : ∀ P, GoodInteriorPoint P → value P ∈ S

/-- Additional unproved E8 application premise: good reduction in the specified CM model. -/
@[expose]
def CMPotentialGoodReduction
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  ∀ P, M.hasPotentiallyGoodReduction P

/-- Additional unproved E8 application premise motivated by Deuring reduction theory. Its exact match to this model is not certified. -/
@[expose]
def DeuringInertSupersingular
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  ∀ ℓ P, M.inertAt ℓ P → M.supersingular (M.reduction P)

/-- Additional unproved E8 application premise: injectivity of the relevant CM-order action after specialization. -/
@[expose]
def CMSpecializationInjective
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  ∀ P, M.specializationInjective P

/-- Compatibility conjunction for the reduction branch. -/
@[expose]
def E8StandardCMReduction
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  CMPotentialGoodReduction M ∧ DeuringInertSupersingular M ∧
    CMSpecializationInjective M

/-- Compatibility interface used by the existing reduction branch.  Its first
conjunct is intentionally *not* used for I22; the pinned declarations
`E8ReducedFormClassification` and `E8IdealClassAction` above replace it there. -/
@[expose]
def E8StandardCM
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  (∀ O, M.actionSimplyTransitive O ∧ M.classCountCorrect O) ∧
    E8StandardCMReduction M

/-- Neutral level-order and covolume data for E9. -/
structure EichlerCovolumeModel (Curve Subgroup Order Lattice Vector : Type*) where
  supersingular : Curve → Prop
  cyclicOfOrderSix : Subgroup → Prop
  preservingOrder : Curve → Subgroup → Order
  isEichlerOfLevelSix : Order → Prop
  independent : Vector → Vector → Vector → Vector → Prop
  span : Vector → Vector → Vector → Vector → Lattice
  covolume : Lattice → ℝ
  squaredNorm : Vector → ℝ

/-- E9 (Arpin): the level-six Eichler-order theorem. -/
@[expose]
def ArpinLevelSix
    {Curve Subgroup Order Lattice Vector : Type*}
    (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop :=
  ∀ E C, M.supersingular E → M.cyclicOfOrderSix C →
    M.isEichlerOfLevelSix (M.preservingOrder E C)

/-- E9 (Goren--Lauter): the general four-vector covolume/Hadamard bound. -/
@[expose]
def GorenLauterHadamard
    {Curve Subgroup Order Lattice Vector : Type*}
    (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop :=
  ∀ a b c d, M.independent a b c d →
    M.covolume (M.span a b c d) ^ 2 ≤
      M.squaredNorm a * M.squaredNorm b *
        M.squaredNorm c * M.squaredNorm d

/-- Compatibility conjunction for older callers. -/
@[expose]
def E9ArpinGorenLauter
    {Curve Subgroup Order Lattice Vector : Type*}
    (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop :=
  ArpinLevelSix M ∧ GorenLauterHadamard M

/-! ## E10--E11: character bounds and standard elementary theory -/

/-- Constancy of a genuine Dirichlet character on `H` consecutive
integers.  `DirichletCharacter` supplies multiplicativity, periodicity and
the extension by zero at non-units; these were missing from the old
arbitrary-function formulation. -/
@[expose]
def ConstantDirichletOnInterval {R : Type*} [CommMonoidWithZero R]
    {ℓ : ℕ} (χ : DirichletCharacter R ℓ) (a : ℤ) (H : ℕ) : Prop :=
  ∀ i j : ℕ, i < H → j < H →
    χ (a + (i : ℤ)) = χ (a + (j : ℤ))

/-- E10 (Treviño, corrected): the all-prime constant-character estimate with
constant `3.38`.  Nonprincipality is the standard condition `χ ≠ 1`,
not a caller-chosen predicate. -/
@[expose]
def E10TrevinoCorrected : Prop :=
  ∀ (ℓ H : ℕ) (χ : DirichletCharacter ℂ ℓ) (a : ℤ),
    ℓ.Prime → χ ≠ 1 → ConstantDirichletOnInterval χ a H →
      (H : ℝ) ≤ 3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ

/-- The independent, general elementary principles grouped under E11.  These
predicates do not contain Rolen's reindexing, cutoff calculation, or
coefficient cancellation. -/
structure ElementaryTheoryModel
    (BinaryForm Character ModularForm : Type*) where
  isPositiveDefinite : BinaryForm → Prop
  isReduced : BinaryForm → Prop
  equivalent : BinaryForm → BinaryForm → Prop
  reciprocityApplies : Character → Prop
  reciprocityConclusion : Character → Prop
  eulerCriterionApplies : Character → Prop
  eulerCriterionConclusion : Character → Prop

/-- E11: reduction of positive definite integral binary quadratic forms,
including the chosen boundary convention. -/
@[expose]
def BinaryQuadraticFormReduction
    {BinaryForm Character ModularForm : Type*}
    (M : ElementaryTheoryModel BinaryForm Character ModularForm) : Prop :=
  ∀ Q, M.isPositiveDefinite Q →
    ∃ Q', M.isReduced Q' ∧ M.equivalent Q Q'

/-- E11: quadratic reciprocity with the modeled sign conventions. -/
@[expose]
def QuadraticReciprocityInput
    {BinaryForm Character ModularForm : Type*}
    (M : ElementaryTheoryModel BinaryForm Character ModularForm) : Prop :=
  ∀ χ, M.reciprocityApplies χ → M.reciprocityConclusion χ

/-- E11: Euler's criterion and the modeled multiplicativity consequence. -/
@[expose]
def EulerCriterionInput
    {BinaryForm Character ModularForm : Type*}
    (M : ElementaryTheoryModel BinaryForm Character ModularForm) : Prop :=
  ∀ χ, M.eulerCriterionApplies χ → M.eulerCriterionConclusion χ

/-- The operations occurring in the general finite-height Stokes theorem.
An input comprises a qualified weakly holomorphic form together with a
harmonic-Maass completion.  The remaining fields are the actual numerical
quantities in the truncated identity; in particular, the conclusion is not
hidden behind an application-chosen predicate. -/
structure FiniteHeightStokesModel (Input : Type*) where
  qualified : Input → Prop
  shadowScale : Input → ℝ
  truncatedIntegral : Input → ℕ → ℝ
  holomorphicConstantTerm : Input → ℝ
  topBoundaryError : Input → ℕ → ℝ
  regularizedPairing : Input → ℝ

/-- The exact output of finite-height Stokes: the truncated-domain identity,
convergence to the regularized pairing, and decay of the nonholomorphic top
boundary. -/
@[expose]
def FiniteHeightStokesConclusion {Input : Type*}
    (M : FiniteHeightStokesModel Input) (x : Input) : Prop :=
  (∀ T, M.shadowScale x * M.truncatedIntegral x T =
      M.holomorphicConstantTerm x + M.topBoundaryError x T) ∧
    Filter.Tendsto (M.truncatedIntegral x) Filter.atTop
      (nhds (M.regularizedPairing x)) ∧
    Filter.Tendsto (M.topBoundaryError x) Filter.atTop (nhds 0)

/-- E11: the general finite-height Stokes theorem, with its full numerical
identity and both limiting assertions exposed. -/
@[expose]
def FiniteHeightStokesTheorem {Input : Type*}
    (M : FiniteHeightStokesModel Input) : Prop :=
  ∀ x, M.qualified x → FiniteHeightStokesConclusion M x

/-- Compatibility conjunction for older callers. -/
@[expose]
def E11ElementaryTheory
    {BinaryForm Character ModularForm StokesInput : Type*}
    (M : ElementaryTheoryModel BinaryForm Character ModularForm)
    (S : FiniteHeightStokesModel StokesInput) : Prop :=
  BinaryQuadraticFormReduction M ∧ QuadraticReciprocityInput M ∧
    EulerCriterionInput M ∧ FiniteHeightStokesTheorem S

/-- A single ledger object with one proof field for every atomic external node
in E1--E11.  In particular, callers can depend on (for example) Deuring
without also importing an opaque conjunction containing class counts. -/
structure RolenLiterature
    {K : Type*} [Field K]
    {IntegralBase CMValueI CMValueJ : Type*} [CommRing IntegralBase]
    (cmValueX : CMValueI → ℂ) (cmValueY : CMValueJ → ℂ)
    {Completion Series Form Input Product Divisor Theta Scalar Cusp
      Exponent Quotient OrderValue Curve Order IdealClass CMPoint Reduction
      Endomorphism Subgroup Lattice Vector Character BinaryForm
      StokesInput : Type*}
    (HM : HarmonicMaassModel Completion Series) (f eta : Series)
    (shadowNormalization : Series → Series)
    (MF : StandardModularFormModel Form)
    (BO : BorcherdsLiftModel Input Product Divisor)
    (WV : WeylVectorModel Input Theta Scalar Cusp)
    (LZ : LigozatModel Exponent Quotient Cusp OrderValue Curve)
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism)
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice Vector)
    (EL : ElementaryTheoryModel BinaryForm Character Form)
    (ST : FiniteHeightStokesModel StokesInput) where
  e1Andrews5 : Andrews5
  e1Andrews7 : Andrews7
  e1Andrews13 : Andrews13
  e2FiniteExclusion : E2AhlgrenKimFiniteExclusion
  e2ThetaCycle : E2AhlgrenKimThetaCycle
  e3Completion : BringmannCompletion HM f eta shadowNormalization
  e3HeckeShadow : HeckeShadowIntertwining HM
  e4Eta : DedekindEtaFoundations MF
  e4J : ModularInvariantFoundations MF
  e4Eisenstein : EisensteinFoundations MF
  e4PrincipalIntegrality : PrincipalPartIntegrality MF
  e4Hecke : GeneralModularHeckeLaws MF
  e4WeightTwoResidue : WeightTwoResidueTheorem MF
  e4PublishedGrid : PublishedMockModularGrid K
  e5 : E5BruinierOno BO
  e6 : E6BruinierSchwagenscheidt WV
  e7Ligozat : LigozatEtaQuotients LZ
  e7IntegralModel : X0SixGoodIntegralModel LZ
  e7GenusZero : X0SixGenusZeroFibers LZ
  e7Cusps : X0SixDisjointCusps LZ
  e8ClassAction : CMClassAction CM
  e8ClassCount : CMClassCount CM
  e8NegativeQuadraticOrderDomain :
    ∀ n : ℕ, E8NegativeQuadraticOrderDomain n
  e8ReducedFormClassification :
    ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
      E8ReducedFormClassification n
  e8FourOrientedFormClassification :
    ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
      E8FourOrientedFormClassification n
  e8GoodReduction : CMPotentialGoodReduction CM
  e8Deuring : DeuringInertSupersingular CM
  e8SpecializationInjective : CMSpecializationInjective CM
  e8IntegralCMClassField :
    E8IntegralCMClassFieldExistence IntegralBase CMValueI CMValueJ
      cmValueX cmValueY
  e9Arpin : ArpinLevelSix EC
  e9GorenLauter : GorenLauterHadamard EC
  e10 : E10TrevinoCorrected
  e11Reduction : BinaryQuadraticFormReduction EL
  e11Reciprocity : QuadraticReciprocityInput EL
  e11EulerCriterion : EulerCriterionInput EL
  e11Stokes : FiniteHeightStokesTheorem ST
  e11SquarefreeCusps : SquarefreeGammaZeroCuspClassification

end SptCM.RolenLiterature
