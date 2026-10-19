import blessed.SptCM.Literature.Repair.UniformLedger
import blessed.SptCM.CM.Repaired.ActualCoordinateConstruction
import blessed.SptCM.Repair.I15ActualCoordinate
import blessed.SptCM.Repair.ActualWronskianContradiction

/-!
# Uniform, source-facing literature ledger

The original all-purpose literature record fixes one pair of CM-value
families.  That is not enough for the final argument, where the discriminant
is chosen only after the prime.  This module records the genuinely uniform
parts of the literature boundary and proves the strongest family-level
construction currently justified by them.

No field below asserts a normalized Borcherds-product identity, a collision
or separation statement, a Wronskian conclusion, a large-prime exclusion, or
the final classification.
-/

namespace SptCM.RolenLiterature.Repair

noncomputable section

open SptCM.CM.Repaired

/-- The carrier models supplied by the good-reduction and inertness part of
E8 at one eligible prime and discriminant.  This record stops strictly before
the Eichler-order argument: it contains no subgroup, covolume, collision,
separation, or Wronskian datum. -/
structure E8ActualReductionModel
    {n h ℓ : ℕ} [Fact ℓ.Prime]
    (C : ActualOrientedCMCoordinates n h)
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (F : C.IntegralFiniteGaloisRealization L)
    (h6 : IsUnit (6 : ZMod ℓ))
    (Sres : E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ h6)) where
  Order : Type
  IdealClass : Type
  CMPoint : Type
  Reduction : Type
  Dq : Type
  [divisionRingDq : DivisionRing Dq]
  [starDq : Star Dq]
  [algebraDq : Algebra ℚ Dq]
  CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq
  standardCM : E8StandardCM CM
  orientedQuadratic : E8OrientedQuadraticSpecialization n CM
  goodReduction :
    E8ActualHauptmodulGoodReduction C F Sres CM orientedQuadratic
  rawPointInert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
    CM.inertAt ℓ (orientedQuadratic.point r Q)

/-- The source-facing E9 model and the comparison maps which say that its
curve, level structure, and preserving order are the ones occurring in the
E8 specialization.  Its characteristic law is stated for every point of the
fiber, and its order comparison for every CM point; the application-specific
`hchar`, `hcyclic`, and `hlevelOrder` functions are derived below.

The fields are general Arpin/Goren--Lauter and integral-lattice laws.  In
particular, no distinguished pair of endomorphisms and no volume inequality
is stored here. -/
structure E9ActualLevelSixModel
    {n ℓ : ℕ}
    {Order IdealClass CMPoint Reduction Dq : Type*}
    [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq)
    (E8Q : E8OrientedQuadraticSpecialization n CM) where
  Subgroup : Type
  Lattice : Type
  covolumeModel :
    EichlerCovolumeModel Reduction Subgroup (Subring Dq) Lattice Dq
  arpinGorenLauter : E9ArpinGorenLauter covolumeModel
  latticeArithmetic : SptCM.Repair.EichlerLatticeArithmetic covolumeModel
  levelSubgroupAt : CMPoint → Subgroup
  supersingularCompatible : ∀ P,
    CM.supersingular P → covolumeModel.supersingular P
  fiberCharacteristic : ∀ P,
    latticeArithmetic.characteristic (CM.reduction P) = ℓ
  cyclicLevelSubgroup : ∀ P,
    covolumeModel.cyclicOfOrderSix (levelSubgroupAt P)
  preservingOrderComparison : ∀ P,
    E8Q.levelOrder =
      covolumeModel.preservingOrder (CM.reduction P) (levelSubgroupAt P)
  inOrderComparison : ∀ O x,
    latticeArithmetic.inOrder O x ↔ x ∈ O

namespace E9ActualLevelSixModel

variable {n ℓ : ℕ}
  {Order IdealClass CMPoint Reduction Dq : Type*}
  [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
  {CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq}
  {E8Q : E8OrientedQuadraticSpecialization n CM}

/-- The level-six subgroup attached to the numerator point of an actual
geometric specialization. -/
def levelSubgroup
    (M : E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
    (S : SptCM.Repair.GeometricCMSpecialization CM) : M.Subgroup :=
  M.levelSubgroupAt S.numeratorPoint

/-- The characteristic comparison needed by I20 is a specialization of the
general fiber-characteristic law, not an extra application assumption. -/
theorem characteristic_eq
    (M : E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
    (S : SptCM.Repair.GeometricCMSpecialization CM) :
    M.latticeArithmetic.characteristic (CM.reduction S.numeratorPoint) = ℓ :=
  M.fiberCharacteristic S.numeratorPoint

/-- Cyclicity of the application subgroup follows from the general
level-subgroup construction. -/
theorem cyclic
    (M : E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
    (S : SptCM.Repair.GeometricCMSpecialization CM) :
    M.covolumeModel.cyclicOfOrderSix (M.levelSubgroup S) :=
  M.cyclicLevelSubgroup S.numeratorPoint

/-- The order comparison consumed by I20 follows by evaluating the general
E8--E9 preserving-order comparison at the numerator CM point. -/
theorem preservingOrder_eq
    (M : E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
    (S : SptCM.Repair.GeometricCMSpecialization CM) :
    E8Q.levelOrder =
      M.covolumeModel.preservingOrder
        (CM.reduction S.numeratorPoint) (M.levelSubgroup S) :=
  M.preservingOrderComparison S.numeratorPoint

/-- The exact local covolume normalization is derived by combining Arpin's
level-six theorem, the two general local-index computations, and the
fiber-characteristic comparison.  This is an equality for the ambient order
lattice, not the four-vector Hadamard inequality used later. -/
theorem preservingOrder_covolume_eq
    (M : E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
    (S : SptCM.Repair.GeometricCMSpecialization CM) :
    M.covolumeModel.covolume
        (M.latticeArithmetic.orderLattice
          (M.covolumeModel.preservingOrder
            (CM.reduction S.numeratorPoint) (M.levelSubgroup S))) =
      6 * ℓ := by
  have hss : M.covolumeModel.supersingular
      (CM.reduction S.numeratorPoint) :=
    M.supersingularCompatible _ S.supersingular
  have hEichler := M.arpinGorenLauter.1
    (CM.reduction S.numeratorPoint) (M.levelSubgroup S) hss (M.cyclic S)
  rw [M.latticeArithmetic.preservingOrder_covolume_eq_six_characteristic
    (CM.reduction S.numeratorPoint) (M.levelSubgroup S) hEichler,
    M.characteristic_eq S]

end E9ActualLevelSixModel

/-- Public, discriminant-uniform literature data which do not depend on an
implementation choice for the analytic Borcherds and quaternionic models.

The class-field field is dependent on the *actual* coordinate family.  This
is essential: it prevents a single unrelated pair of CM-value families from
being used for every discriminant. -/
structure UniformRolenLiterature where
  arithmetic : UniformArithmeticLiterature
  e4e7HauptmodulTransformation : E4E7AnalyticHauptmodulTransformation
  e7ActualIntegralCoordinate : SptCM.Repair.E7ActualX0SixApplicationChecks
  e8NegativeQuadraticOrderDomain :
    ∀ n : ℕ, E8NegativeQuadraticOrderDomain n
  e8ReducedFormClassification :
    ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
      E8ReducedFormClassification n
  e8FourOrientedFormClassification :
    ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)],
      E8FourOrientedFormClassification n
  e8IntegralCMClassField :
    ∀ (n h : ℕ), Squarefree n → n % 24 = 23 →
      ∀ C : ActualOrientedCMCoordinates n h,
      ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
          (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
        Nonempty (E8FiniteGaloisIntegralCMReciprocity AwaySix
          (C.orientation1.Index ⊕ C.orientation11.Index)
          (C.orientation5.Index ⊕ C.orientation7.Index) L
          C.numeratorRoot C.denominatorRoot)
  e8ActualReduction :
    ∀ {n ℓ : ℕ} [Fact ℓ.Prime]
      (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
      (hinert : legendreSym ℓ (-(n : ℤ)) = -1)
      (C : ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n))
      (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (F : C.IntegralFiniteGaloisRealization L)
      (h6 : IsUnit (6 : ZMod ℓ))
      (Sres : E8IntegralClosureResidueSpecialization
        L (AlgebraicClosure (ZMod ℓ)) ℓ
        (SptCM.awaySixReduction ℓ h6)),
      Nonempty (E8ActualReductionModel C F h6 Sres)
  e9ActualLevelSix :
    ∀ {n h ℓ : ℕ} [Fact ℓ.Prime]
      (C : ActualOrientedCMCoordinates n h)
      (Order IdealClass CMPoint Reduction Dq : Type)
      (_ : DivisionRing Dq) (_ : Star Dq) (_ : Algebra ℚ Dq)
      (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq)
      (E8Q : E8OrientedQuadraticSpecialization n CM),
      Nonempty (E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)

/-- The exact E1 input is available without passing through any analytic or
CM application model. -/
theorem UniformRolenLiterature.e1
    (lit : UniformRolenLiterature) : E1AndrewsCongruences :=
  lit.arithmetic.e1

/-- The finite Ahlgren--Kim theorem is an atomic projection of the uniform
ledger. -/
theorem UniformRolenLiterature.e2Finite
    (lit : UniformRolenLiterature) : E2AhlgrenKimFiniteExclusion :=
  lit.arithmetic.e2Finite

/-- The corrected Treviño theorem is an atomic projection of the uniform
ledger. -/
theorem UniformRolenLiterature.e10
    (lit : UniformRolenLiterature) : E10TrevinoCorrected :=
  lit.arithmetic.e10

/-- The E7 application checks really do construct the actual integral
Hauptmodul coordinate; that conclusion is not stored in the ledger. -/
theorem UniformRolenLiterature.actualHauptmodulIntegralCoordinate
    (lit : UniformRolenLiterature) :
    SptCM.Repair.ActualHauptmodulIntegralCoordinate :=
  SptCM.Repair.exists_actualHauptmodul_integral_coordinate
    lit.e7ActualIntegralCoordinate

/-- For every discriminant in the range used by the paper, the uniform E4/E7
transformation law and E8 form classifications construct the genuine four
oriented analytic coordinate families. -/
theorem UniformRolenLiterature.actualCoordinates
    (lit : UniformRolenLiterature) {n : ℕ}
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23) :
    Nonempty (ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n)) :=
  exists_actualOrientedCMCoordinates_of_E4_E7_E8 hsquarefree hmod
    (lit.e8NegativeQuadraticOrderDomain n)
    (lit.e8ReducedFormClassification n)
    (lit.e8FourOrientedFormClassification n)
    lit.e4e7HauptmodulTransformation

/-- An eligible-discriminant package retaining the actual class field and
its integral realization.  The field is allowed to depend on `n`; requiring
one fixed number field for all discriminants would not be a source theorem. -/
def ActualCMClassFieldPackage (n : ℕ) : Prop :=
  ∃ (C : ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n))
      (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Nonempty (C.IntegralFiniteGaloisRealization L)

/-- The uniform ledger produces a genuine integral class-field realization at
each eligible discriminant, with the field chosen only after `n`. -/
theorem UniformRolenLiterature.actualCMClassFieldPackage
    (lit : UniformRolenLiterature) {n : ℕ}
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23) :
    ActualCMClassFieldPackage n := by
  let C := Classical.choice (lit.actualCoordinates hsquarefree hmod)
  rcases lit.e8IntegralCMClassField n (SptCM.negativeClassNumber n)
      hsquarefree hmod C with
    ⟨L, instField, instRat, instFinite, instGalois, hclassField⟩
  letI : Field L := instField
  letI : Algebra ℚ L := instRat
  letI : FiniteDimensional ℚ L := instFinite
  letI : IsGalois ℚ L := instGalois
  exact ⟨C, L, instField, instRat, instFinite, instGalois,
    ⟨ActualOrientedCMCoordinates.IntegralFiniteGaloisRealization.ofE8 C
      (Classical.choice hclassField)⟩⟩

/-- The dependent E8 class-field theorem then constructs the descended
integral class-polynomial specification for those actual CM values.  The
polynomials and their coefficient descent are deductions, not ledger fields.
-/
theorem UniformRolenLiterature.actualClassPolynomialPackage
    (lit : UniformRolenLiterature) {n : ℕ}
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23) :
    Nonempty (Σ C : ActualOrientedCMCoordinates n
      (SptCM.negativeClassNumber n), ActualClassPolynomialSpec C) := by
  let C := Classical.choice (lit.actualCoordinates hsquarefree hmod)
  rcases lit.e8IntegralCMClassField n (SptCM.negativeClassNumber n)
      hsquarefree hmod C with
    ⟨L, instField, instRat, instFinite, instGalois, hclassField⟩
  letI : Field L := instField
  letI : Algebra ℚ L := instRat
  letI : FiniteDimensional ℚ L := instFinite
  letI : IsGalois ℚ L := instGalois
  let E := Classical.choice hclassField
  exact ⟨⟨C, (ActualOrientedCMCoordinates.IntegralFiniteGaloisRealization.ofE8 C E).actualClassPolynomialSpec⟩⟩

/-- The exact E8 and E9 source models assemble the pointwise application
package used by the later argument.  Only carrier choices and upstream
theorems are copied into the package.  In particular:

* the integral-closure specialization is obtained from the general E8
  residue theorem;
* the coordinate specialization and point comparison remain constructions
  of `E8ActualHauptmodulGoodReduction` (and are not package fields);
* `hchar`, cyclicity, and `hlevelOrder` are derived by specializing the
  general E9 comparison laws;
* the local factor `2 * 3 = 6` and the resulting preserving-order covolume
  are theorems of `EichlerLatticeArithmetic`, rather than application data.

There is no separation, Wronskian, volume inequality, or final conclusion in
this assembly theorem. -/
theorem UniformRolenLiterature.actualCMApplicationPackage
    (lit : UniformRolenLiterature) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hfive : 5 ≤ ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    let h6 := SptCM.six_isUnit_zmod_of_prime_five_le
      (Fact.out : ℓ.Prime) hfive
    Nonempty (Σ C : ActualOrientedCMCoordinates n
      (SptCM.negativeClassNumber n),
      SptCM.Repair.ActualCMApplicationPackage C h6) := by
  let h6 := SptCM.six_isUnit_zmod_of_prime_five_le
    (Fact.out : ℓ.Prime) hfive
  let C := Classical.choice (lit.actualCoordinates hsquarefree hmod)
  rcases lit.e8IntegralCMClassField n (SptCM.negativeClassNumber n)
      hsquarefree hmod C with
    ⟨L, instField, instRat, instFinite, instGalois, hclassField⟩
  letI : Field L := instField
  letI : Algebra ℚ L := instRat
  letI : FiniteDimensional ℚ L := instFinite
  letI : IsGalois ℚ L := instGalois
  let F : C.IntegralFiniteGaloisRealization L :=
    ActualOrientedCMCoordinates.IntegralFiniteGaloisRealization.ofE8 C
      (Classical.choice hclassField)
  let Sres : E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ h6) :=
    Classical.choice
      (lit.arithmetic.e8Residue ℓ h6 L instField inferInstance instRat
        instFinite)
  let M : E8ActualReductionModel C F h6 Sres :=
    Classical.choice
      (lit.e8ActualReduction hsquarefree hmod hinert C L instField instRat
        instFinite instGalois F h6 Sres)
  letI : DivisionRing M.Dq := M.divisionRingDq
  letI : Star M.Dq := M.starDq
  letI : Algebra ℚ M.Dq := M.algebraDq
  let N : E9ActualLevelSixModel (ℓ := ℓ) M.CM M.orientedQuadratic :=
    Classical.choice
      (lit.e9ActualLevelSix C M.Order M.IdealClass M.CMPoint M.Reduction
        M.Dq M.divisionRingDq M.starDq M.algebraDq M.CM
        M.orientedQuadratic)
  exact ⟨⟨C, {
    L := L
    Order := M.Order
    IdealClass := M.IdealClass
    CMPoint := M.CMPoint
    Reduction := M.Reduction
    Dq := M.Dq
    Subgroup := N.Subgroup
    Lattice := N.Lattice
    fieldL := instField
    algebraL := instRat
    finiteDimensionalL := instFinite
    isGaloisL := instGalois
    divisionRingDq := M.divisionRingDq
    starDq := M.starDq
    algebraDq := M.algebraDq
    F := F
    Sres := Sres
    CM := M.CM
    hE8 := M.standardCM
    E8Q := M.orientedQuadratic
    Hgood := M.goodReduction
    rawPointInert := M.rawPointInert
    EC := N.covolumeModel
    hE9 := N.arpinGorenLauter
    Arith := N.latticeArithmetic
    levelSubgroup := N.levelSubgroup
    supersingularCompatible := N.supersingularCompatible
    hchar := N.characteristic_eq
    hcyclic := N.cyclic
    hlevelOrder := N.preservingOrder_eq
    hinOrder := N.inOrderComparison }⟩⟩

/-- The application package and the class polynomials descended from its
*same* integral Galois realization.

Keeping these objects in one dependent package is important.  If the
coordinate family and the polynomial family were chosen independently, the
normalized analytic identity could concern different CM values from the
ones to which the E8--E9 reduction argument is applied. -/
theorem UniformRolenLiterature.actualCMPolynomialApplicationPackage
    (lit : UniformRolenLiterature) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hfive : 5 ≤ ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    let h6 := SptCM.six_isUnit_zmod_of_prime_five_le
      (Fact.out : ℓ.Prime) hfive
    Nonempty (Σ C : ActualOrientedCMCoordinates n
        (SptCM.negativeClassNumber n),
      Σ _D : ActualClassPolynomialSpec C,
        SptCM.Repair.ActualCMApplicationPackage C h6) := by
  let h6 := SptCM.six_isUnit_zmod_of_prime_five_le
    (Fact.out : ℓ.Prime) hfive
  let Q := Classical.choice
    (lit.actualCMApplicationPackage hfive hsquarefree hmod hinert)
  let C := Q.1
  let A := Q.2
  letI : Field A.L := A.fieldL
  letI : Algebra ℚ A.L := A.algebraL
  letI : FiniteDimensional ℚ A.L := A.finiteDimensionalL
  letI : IsGalois ℚ A.L := A.isGaloisL
  let D : ActualClassPolynomialSpec C :=
    A.F.actualClassPolynomialSpec
  exact ⟨⟨C, D, A⟩⟩

/-!
The analytic E3--E6 models are deliberately not fields of this literature
ledger.  `Repair.PublicLargeExclusion` combines them with the dependent
package above only after E10 has selected an eligible discriminant.  In
particular, neither one class field nor one quaternion algebra is required to
serve all discriminants and primes.
-/

end

end SptCM.RolenLiterature.Repair
