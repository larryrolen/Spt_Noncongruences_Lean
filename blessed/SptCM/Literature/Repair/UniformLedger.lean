import blessed.SptCM.Literature.RolenLiterature
import blessed.SptCM.CM.Repaired.I16Coordinates
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.RatFunc.Defs

/-!
# A nonvacuous uniform literature boundary

This module repairs an important typing issue in the first version of the E8
ledger.  Reduction modulo a prime is a homomorphism on an integral model (or
on a localization of it), not on its characteristic-zero fraction field.
In particular, there is no unital ring homomorphism from a number field to a
field of positive characteristic.

The structures below state the standard CM residue theorem on the integral
closure of `ℤ[1/6]` in the number field.  They contain no common-root,
collision, separation, Wronskian, or classification conclusion.
-/

namespace SptCM.RolenLiterature.Repair

noncomputable section

open SptCM.CM.Repaired

/-- A good-prime residue map is defined on the integral closure, not on the
whole number field.  Compatibility says that it extends the chosen reduction
of `ℤ[1/6]` coefficientwise. -/
structure E8IntegralClosureResidueSpecialization
    (L k : Type*) (ℓ : ℕ)
    [Field L] [Algebra AwaySix L]
    [Field k] [Algebra (ZMod ℓ) k]
    (coefficientReduction : AwaySix →+* ZMod ℓ) where
  residue : integralClosure AwaySix L →+* k
  compatible :
    residue.comp (algebraMap AwaySix (integralClosure AwaySix L)) =
      (algebraMap (ZMod ℓ) k).comp coefficientReduction

/-- Reduce an element after supplying the mathematically necessary proof that
it is integral over `ℤ[1/6]`. -/
def E8IntegralClosureResidueSpecialization.reduce
    {L k : Type*} {ℓ : ℕ}
    [Field L] [Algebra AwaySix L]
    [Field k] [Algebra (ZMod ℓ) k]
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization
      L k ℓ coefficientReduction)
    (x : L) (hx : IsIntegral AwaySix x) : k :=
  S.residue ⟨x, hx⟩

/-- The residue map agrees with coefficient reduction on constants. -/
theorem E8IntegralClosureResidueSpecialization.reduce_algebraMap
    {L k : Type*} {ℓ : ℕ}
    [Field L] [Algebra AwaySix L]
    [Field k] [Algebra (ZMod ℓ) k]
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization
      L k ℓ coefficientReduction)
    (a : AwaySix) :
    S.residue (algebraMap AwaySix (integralClosure AwaySix L) a) =
      algebraMap (ZMod ℓ) k (coefficientReduction a) := by
  exact DFunLike.congr_fun S.compatible a

/-- Source-faithful E8 lying-over/residue theorem in precisely the good-prime
coefficient ring needed by the paper.  The theorem only produces a residue
map on the integral closure.  Root collisions and polynomial separation are
not part of this external statement. -/
def E8AwaySixIntegralClosureResidueTheorem : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    (L : Type) (_ : Field L) (_ : Algebra AwaySix L)
    (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L),
      Nonempty (E8IntegralClosureResidueSpecialization
        L (AlgebraicClosure (ZMod ℓ)) ℓ
        (SptCM.awaySixReduction ℓ h6))

/-- Reduction of the first CM family through the corrected integral
closure residue map.  This is the direct replacement for applying a
(nonexistent) residue homomorphism to the ambient number field. -/
def E8FiniteGaloisIntegralCMReciprocity.reducedX
    {I J L k : Type*} {ℓ : ℕ}
    [Field L] [Algebra AwaySix L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [Field k] [Algebra (ZMod ℓ) k]
    {x : I → ℂ} {y : J → ℂ}
    (E : E8FiniteGaloisIntegralCMReciprocity AwaySix I J L x y)
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization
      L k ℓ coefficientReduction) (i : I) : k :=
  S.reduce (E.toE8FiniteGaloisCMReciprocity.algebraicX i) (E.integralX i)

/-- Reduction of the second CM family through the corrected integral closure
residue map. -/
def E8FiniteGaloisIntegralCMReciprocity.reducedY
    {I J L k : Type*} {ℓ : ℕ}
    [Field L] [Algebra AwaySix L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [Field k] [Algebra (ZMod ℓ) k]
    {x : I → ℂ} {y : J → ℂ}
    (E : E8FiniteGaloisIntegralCMReciprocity AwaySix I J L x y)
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization
      L k ℓ coefficientReduction) (j : J) : k :=
  S.reduce (E.toE8FiniteGaloisCMReciprocity.algebraicY j) (E.integralY j)

/-- Lift every numerator root of an actual integral finite-Galois
realization to the integral closure. -/
def integralNumeratorRoot
    {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (F : C.IntegralFiniteGaloisRealization L)
    (i : C.orientation1.Index ⊕ C.orientation11.Index) :
    integralClosure AwaySix L :=
  ⟨F.toFiniteGaloisRealization.numeratorAlgebraicRoot i,
    (mem_integralClosure_iff AwaySix L).mpr (F.integralNumerator i)⟩

/-- Lift every denominator root of an actual integral finite-Galois
realization to the integral closure. -/
def integralDenominatorRoot
    {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (F : C.IntegralFiniteGaloisRealization L)
    (i : C.orientation5.Index ⊕ C.orientation7.Index) :
    integralClosure AwaySix L :=
  ⟨F.toFiniteGaloisRealization.denominatorAlgebraicRoot i,
    (mem_integralClosure_iff AwaySix L).mpr (F.integralDenominator i)⟩

/-- Correct specialization of an actual numerator CM root. -/
def specializedActualNumeratorRoot
    {n h ℓ : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    {L k : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    [Field k] [Algebra (ZMod ℓ) k]
    (F : C.IntegralFiniteGaloisRealization L)
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization L k ℓ coefficientReduction)
    (i : C.orientation1.Index ⊕ C.orientation11.Index) : k :=
  S.residue (integralNumeratorRoot F i)

/-- Correct specialization of an actual denominator CM root. -/
def specializedActualDenominatorRoot
    {n h ℓ : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    {L k : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    [Field k] [Algebra (ZMod ℓ) k]
    (F : C.IntegralFiniteGaloisRealization L)
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralClosureResidueSpecialization L k ℓ coefficientReduction)
    (i : C.orientation5.Index ⊕ C.orientation7.Index) : k :=
  S.residue (integralDenominatorRoot F i)

/-- A characteristic-zero field cannot itself admit the positive-characteristic
residue map used in the old interface.  This theorem makes the typing defect
explicit rather than silently retaining a vacuous premise. -/
theorem no_numberField_to_positiveCharacteristic_residue
    {L k : Type*} {ℓ : ℕ}
    [Field L] [CharZero L] [Field k] [CharP k ℓ]
    (hℓ : ℓ.Prime) (f : L →+* k) : False := by
  have hzeroK : (ℓ : k) = 0 := by
    exact CharP.cast_eq_zero k ℓ
  have hmap : f (ℓ : L) = 0 := by
    simpa using hzeroK
  have hzeroL : (ℓ : L) = 0 := f.injective (by simpa using hmap)
  exact (Nat.cast_ne_zero.mpr hℓ.ne_zero) hzeroL

/-- In the precise parameter regime used by the old I18 interface,
the old field-valued specialization record is uninhabited. -/
theorem old_E8IntegralCMResidueSpecialization_false
    {L k : Type*} {ℓ : ℕ} [Fact ℓ.Prime]
    [Field L] [CharZero L] [Field k] [Algebra (ZMod ℓ) k]
    {coefficientReduction : AwaySix →+* ZMod ℓ}
    (S : E8IntegralCMResidueSpecialization
      AwaySix L k ℓ coefficientReduction) : False := by
  letI : CharP k ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) k).injective ℓ
  exact no_numberField_to_positiveCharacteristic_residue
    (Fact.out : ℓ.Prime) S.residue

/-- Correct E7 ledger addendum.  These are general geometric laws;
the explicit cusp-order calculation and identification of the eta quotient
with Rolen's `t` are intentionally not fields. -/
structure E7IntegralGeometryLiterature
    {Function Divisor Curve Section Expansion Order : Type*}
    [Zero Order] [One Order] [Neg Order]
    (G : IntegralCurveFunctionGeometry
      Function Divisor Curve Section Expansion)
    (isIntegralModel hasGenusZeroFibers
      hasDisjointStandardCuspSections : Curve → Prop)
    (isRationalFunction : Function → Prop)
    (cuspOrder : Function → Section → Order) where
  horizontalDivisor : E7HorizontalDivisorPrinciple G
    isIntegralModel hasGenusZeroFibers isRationalFunction cuspOrder
  noVerticalComponent : E7NoVerticalComponentPrinciple G
    isIntegralModel hasDisjointStandardCuspSections
  degreeOne : E7IntegralDegreeOneCriterion G
    isIntegralModel hasGenusZeroFibers hasDisjointStandardCuspSections

/-- Correct E8 ledger addendum for a fixed standard CM reduction model.
The specialization theorem is restricted to the negative fundamental
level-six discriminants where it is used.  No collision, commutator, volume,
or separation result is included. -/
structure E8OrientedReductionLiterature
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D) where
  potentiallyGood : CMPotentialGoodReduction CM
  deuring : DeuringInertSupersingular CM
  specializationInjective : CMSpecializationInjective CM
  negativeOrderDomain : ∀ n, E8NegativeQuadraticOrderDomain n
  reducedForms : ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
    E8ReducedFormClassification n
  orientedForms : ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
    E8FourOrientedFormClassification n
  orientedSpecialization : ∀ n,
    IsNegativeFundamentalDiscriminant n → n % 24 = 23 →
      Nonempty (E8OrientedQuadraticSpecialization n CM)

/-- The nonvacuous E8 reduction conjunction needed by the common-root
specialization branch. -/
theorem E8OrientedReductionLiterature.standardReduction
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    {CM : CMTheoryModel Order IdealClass CMPoint Reduction D}
    (lit : E8OrientedReductionLiterature CM) :
    E8StandardCMReduction CM :=
  ⟨lit.potentiallyGood, lit.deuring, lit.specializationInjective⟩

/-- Atomic public ledger entries which are already independent of any choice
of analytic or geometric model.  The more elaborate E3--E9 and E11 results
remain parameterized by their source models in `RolenLiterature`; this record
must not turn those application models into arbitrary universally quantified
claims. -/
structure UniformArithmeticLiterature where
  e1 : E1AndrewsCongruences
  e2Finite : E2AhlgrenKimFiniteExclusion
  e2ThetaCycle : E2AhlgrenKimThetaCycle
  e8Residue : E8AwaySixIntegralClosureResidueTheorem
  e10 : E10TrevinoCorrected
  e11SquarefreeCusps : SquarefreeGammaZeroCuspClassification

/-- Projection to the exact E1 conjunction used by final assembly. -/
theorem UniformArithmeticLiterature.andrews
    (lit : UniformArithmeticLiterature) : E1AndrewsCongruences :=
  lit.e1

/-- Projection to the exact finite Ahlgren--Kim exclusion. -/
theorem UniformArithmeticLiterature.finiteExclusion
    (lit : UniformArithmeticLiterature) : E2AhlgrenKimFiniteExclusion :=
  lit.e2Finite

/-- Projection to the corrected Treviño theorem. -/
theorem UniformArithmeticLiterature.trevino
    (lit : UniformArithmeticLiterature) : E10TrevinoCorrected :=
  lit.e10

end

end SptCM.RolenLiterature.Repair
