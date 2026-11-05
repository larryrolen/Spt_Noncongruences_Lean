module

public import blessed.SptCM.Quaternion.Repaired.I19ActualAdapter

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Constructing the actual oriented reduction points

This module removes the presentation-comparison premise from the actual-index
adapter.  The sole geometric comparison input is the uniform good-reduction
law for the Hauptmodul: evaluation after reduction agrees with reduction of
an integral lift of its characteristic-zero value.  It is stated for every
raw oriented form and every integral lift, rather than as four identities for
chosen finite enumerations.
-/

namespace SptCM.CM.Repaired

noncomputable section

open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair

/-- The good-reduction evaluation law for the actual Hauptmodul on oriented
CM points.  If an integral class-field element has the analytic Hauptmodul
value at a raw CM point, then its residue is the regular coordinate of the
reduction of that same CM point.  This is uniform in the orientation and raw
form and contains no collision, action, commutator, covolume, or separation
assertion. -/
structure E8ActualHauptmodulGoodReduction
    {n h ℓ : ℕ} (C : ActualOrientedCMCoordinates n h)
    {L k Order IdealClass CMPoint Reduction D : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [Field k] [Algebra (ZMod ℓ) k]
    [DivisionRing D] [Star D]
    (F : C.IntegralFiniteGaloisRealization L)
    {coefficientReduction : SptCM.AwaySix →+* ZMod ℓ}
    (Sres : E8IntegralClosureResidueSpecialization L k ℓ
      coefficientReduction)
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (E8Q : E8OrientedQuadraticSpecialization n CM) where
  coordinate : Reduction → k
  coordinate_injective : Function.Injective coordinate
  reduction_evaluation : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r)
      (z : integralClosure SptCM.AwaySix L),
    F.embedding z.1 =
        analyticHauptmodul (rawCMUpperHalfPlane C.n_pos Q) →
      coordinate (CM.reduction (E8Q.point r Q)) = Sres.residue z

end

end SptCM.CM.Repaired

namespace SptCM.CM.Repaired

noncomputable section

open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair

namespace ActualOrientedCMCoordinates

variable {n h : ℕ} (C : ActualOrientedCMCoordinates n h)

/-- Reductions of the E8 points attached to the canonical raw representatives
of the two numerator orientation families. -/
@[expose]
def actualNumeratorReduction
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (E8Q : E8OrientedQuadraticSpecialization n CM) :
    C.orientation1.Index ⊕ C.orientation11.Index → Reduction
  | .inl i => CM.reduction
      (E8Q.point 1 (rawRepresentative (C.orientation1.classes i)))
  | .inr i => CM.reduction
      (E8Q.point 11 (rawRepresentative (C.orientation11.classes i)))

/-- Reductions of the corresponding denominator points. -/
@[expose]
def actualDenominatorReduction
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (E8Q : E8OrientedQuadraticSpecialization n CM) :
    C.orientation5.Index ⊕ C.orientation7.Index → Reduction
  | .inl i => CM.reduction
      (E8Q.point 5 (rawRepresentative (C.orientation5.classes i)))
  | .inr i => CM.reduction
      (E8Q.point 7 (rawRepresentative (C.orientation7.classes i)))

variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
  [IsGalois ℚ L]

/-- The integral numerator lift indexed by an orientation-one class has the
Hauptmodul value at the canonical raw representative. -/
theorem embedding_integralNumeratorRoot_inl
    (F : C.IntegralFiniteGaloisRealization L) (i : C.orientation1.Index) :
    F.embedding (integralNumeratorRoot F (.inl i)).1 =
      analyticHauptmodul (rawCMUpperHalfPlane C.n_pos
        (rawRepresentative (C.orientation1.classes i))) := by
  calc
    _ = C.numeratorRoot (.inl i) := F.realizesNumerator _
    _ = actualOrientedHauptmodulValue C.invariant1 C.n_pos
        (C.orientation1.classes i) := rfl
    _ = _ := by
      have hrep := congrArg
        (actualOrientedHauptmodulValue C.invariant1 C.n_pos)
        (mk_rawRepresentative (C.orientation1.classes i)).symm
      exact hrep

/-- The orientation-eleven numerator analogue. -/
theorem embedding_integralNumeratorRoot_inr
    (F : C.IntegralFiniteGaloisRealization L) (i : C.orientation11.Index) :
    F.embedding (integralNumeratorRoot F (.inr i)).1 =
      analyticHauptmodul (rawCMUpperHalfPlane C.n_pos
        (rawRepresentative (C.orientation11.classes i))) := by
  calc
    _ = C.numeratorRoot (.inr i) := F.realizesNumerator _
    _ = actualOrientedHauptmodulValue C.invariant11 C.n_pos
        (C.orientation11.classes i) := rfl
    _ = _ := by
      have hrep := congrArg
        (actualOrientedHauptmodulValue C.invariant11 C.n_pos)
        (mk_rawRepresentative (C.orientation11.classes i)).symm
      exact hrep

/-- The orientation-five denominator analogue. -/
theorem embedding_integralDenominatorRoot_inl
    (F : C.IntegralFiniteGaloisRealization L) (i : C.orientation5.Index) :
    F.embedding (integralDenominatorRoot F (.inl i)).1 =
      analyticHauptmodul (rawCMUpperHalfPlane C.n_pos
        (rawRepresentative (C.orientation5.classes i))) := by
  calc
    _ = C.denominatorRoot (.inl i) := F.realizesDenominator _
    _ = actualOrientedHauptmodulValue C.invariant5 C.n_pos
        (C.orientation5.classes i) := rfl
    _ = _ := by
      have hrep := congrArg
        (actualOrientedHauptmodulValue C.invariant5 C.n_pos)
        (mk_rawRepresentative (C.orientation5.classes i)).symm
      exact hrep

/-- The orientation-seven denominator analogue. -/
theorem embedding_integralDenominatorRoot_inr
    (F : C.IntegralFiniteGaloisRealization L) (i : C.orientation7.Index) :
    F.embedding (integralDenominatorRoot F (.inr i)).1 =
      analyticHauptmodul (rawCMUpperHalfPlane C.n_pos
        (rawRepresentative (C.orientation7.classes i))) := by
  calc
    _ = C.denominatorRoot (.inr i) := F.realizesDenominator _
    _ = actualOrientedHauptmodulValue C.invariant7 C.n_pos
        (C.orientation7.classes i) := rfl
    _ = _ := by
      have hrep := congrArg
        (actualOrientedHauptmodulValue C.invariant7 C.n_pos)
        (mk_rawRepresentative (C.orientation7.classes i)).symm
      exact hrep

end ActualOrientedCMCoordinates

end

end SptCM.CM.Repaired

namespace SptCM.CM.Repaired

noncomputable section

open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair

namespace E8ActualHauptmodulGoodReduction

variable {n h ℓ : ℕ} {C : ActualOrientedCMCoordinates n h}
  {L k Order IdealClass CMPoint Reduction D : Type*}
  [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
  [Field k] [Algebra (ZMod ℓ) k]
  [DivisionRing D] [Star D]
  {coefficientReduction : SptCM.AwaySix →+* ZMod ℓ}
  {F : C.IntegralFiniteGaloisRealization L}
  {Sres : E8IntegralClosureResidueSpecialization L k ℓ coefficientReduction}
  {CM : CMTheoryModel Order IdealClass CMPoint Reduction D}
  {E8Q : E8OrientedQuadraticSpecialization n CM}

/-- The uniform evaluation law constructs the entire coordinate-specialization
record, with the points chosen to be reductions of the E8 raw-form points. -/
@[expose]
def coordinateSpecialization
    (H : E8ActualHauptmodulGoodReduction C F Sres CM E8Q) :
    E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) k Reduction
      (fun i => Sres.residue (integralNumeratorRoot F i))
      (fun j => Sres.residue (integralDenominatorRoot F j)) where
  pointX := C.actualNumeratorReduction CM E8Q
  pointY := C.actualDenominatorReduction CM E8Q
  coordinate := H.coordinate
  realizesX i := by
    rcases i with i | i
    · exact H.reduction_evaluation 1
        (rawRepresentative (C.orientation1.classes i)) _
        (C.embedding_integralNumeratorRoot_inl F i)
    · exact H.reduction_evaluation 11
        (rawRepresentative (C.orientation11.classes i)) _
        (C.embedding_integralNumeratorRoot_inr F i)
  realizesY i := by
    rcases i with i | i
    · exact H.reduction_evaluation 5
        (rawRepresentative (C.orientation5.classes i)) _
        (C.embedding_integralDenominatorRoot_inl F i)
    · exact H.reduction_evaluation 7
        (rawRepresentative (C.orientation7.classes i)) _
        (C.embedding_integralDenominatorRoot_inr F i)
  coordinate_injective := H.coordinate_injective

/-- With the standard inertness qualification for these CM points, the CM
reduction interpretation is obtained from the same raw-form points used in
`coordinateSpecialization`.  Inertness is an arithmetic qualification, not a
point-comparison or downstream quaternionic conclusion. -/
@[expose]
def pointReductionData
    (H : E8ActualHauptmodulGoodReduction C F Sres CM E8Q)
    (hinert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
      CM.inertAt ℓ (E8Q.point r Q)) :
    ActualCMPointReductionData CM ℓ
      (H.coordinateSpecialization.pointX)
      (H.coordinateSpecialization.pointY) where
  numeratorPoint
    | .inl i => E8Q.point 1 (rawRepresentative (C.orientation1.classes i))
    | .inr i => E8Q.point 11 (rawRepresentative (C.orientation11.classes i))
  denominatorPoint
    | .inl i => E8Q.point 5 (rawRepresentative (C.orientation5.classes i))
    | .inr i => E8Q.point 7 (rawRepresentative (C.orientation7.classes i))
  realizesNumerator i := by cases i <;> rfl
  realizesDenominator i := by cases i <;> rfl
  numeratorInert i := by
    rcases i with i | i
    · exact hinert 1 (rawRepresentative (C.orientation1.classes i))
    · exact hinert 11 (rawRepresentative (C.orientation11.classes i))
  denominatorInert i := by
    rcases i with i | i
    · exact hinert 5 (rawRepresentative (C.orientation5.classes i))
    · exact hinert 7 (rawRepresentative (C.orientation7.classes i))

/-- Because both records were built from the same raw-form points, their
point identification is now definitional rather than an external comparison
premise. -/
theorem pointIdentification
    (H : E8ActualHauptmodulGoodReduction C F Sres CM E8Q)
    (hinert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
      CM.inertAt ℓ (E8Q.point r Q)) :
    ActualOrientedPointIdentification C CM
      (H.pointReductionData hinert) E8Q where
  numeratorOne _ := rfl
  numeratorEleven _ := rfl
  denominatorFive _ := rfl
  denominatorSeven _ := rfl

/-- Hence the stronger quotient-checked compatibility consumed by I19 is a
theorem, not an E8 application assumption. -/
theorem pointCompatibility
    (H : E8ActualHauptmodulGoodReduction C F Sres CM E8Q)
    (hinert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
      CM.inertAt ℓ (E8Q.point r Q)) :
    ActualOrientedPointCompatibility C CM
      (H.pointReductionData hinert) E8Q :=
  ActualOrientedPointCompatibility.ofIdentification
    (H.pointIdentification hinert)

end E8ActualHauptmodulGoodReduction

end

end SptCM.CM.Repaired

namespace SptCM.CM.Repaired

noncomputable section

open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
open SptCM.Repair

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
  (Dpoly : ActualClassPolynomialSpec C)

/-- The actual separation theorem with the point-presentation comparison
discharged.  The remaining E8 geometric input is the uniform regular-coordinate
evaluation law and the standard inertness qualification of the raw CM points;
the coordinate specialization, reduction data, and all four comparison
equalities are constructed internally. -/
theorem actualClassPolynomials_isCoprime_of_goodReduction_E8_E9
    {L Order IdealClass CMPoint Reduction Dq Subgroup Lattice : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    {ℓ : ℕ} [Fact ℓ.Prime]
    [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ h6))
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq)
    (hE8 : E8StandardCM CM)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (Hgood : E8ActualHauptmodulGoodReduction C F Sres CM E8Q)
    (hinert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
      CM.inertAt ℓ (E8Q.point r Q))
    (EC : EichlerCovolumeModel Reduction Subgroup (Subring Dq) Lattice Dq)
    (hE9 : E9ArpinGorenLauter EC)
    (A : EichlerLatticeArithmetic EC)
    (levelSubgroup : GeometricCMSpecialization CM → Subgroup)
    (supersingularCompatible : ∀ E,
      CM.supersingular E → EC.supersingular E)
    (hchar : ∀ S : GeometricCMSpecialization CM,
      A.characteristic (CM.reduction S.numeratorPoint) = ℓ)
    (hcyclic : ∀ S : GeometricCMSpecialization CM,
      EC.cyclicOfOrderSix (levelSubgroup S))
    (hlevelOrder : ∀ S : GeometricCMSpecialization CM,
      E8Q.levelOrder =
        EC.preservingOrder (CM.reduction S.numeratorPoint) (levelSubgroup S))
    (hinOrder : ∀ O x, A.inOrder O x ↔ x ∈ O)
    (hmod : n % 24 = 23)
    (hsmall : (n + 1) ^ 2 < 24 * ℓ) :
    IsCoprime (Dpoly.A.map (SptCM.awaySixReduction ℓ h6))
      (Dpoly.B.map (SptCM.awaySixReduction ℓ h6)) := by
  exact Dpoly.actualClassPolynomials_isCoprime_of_indexed_E8_E9
    h6 F Sres Hgood.coordinateSpecialization CM hE8
    (Hgood.pointReductionData hinert) E8Q
    (Hgood.pointCompatibility hinert) EC hE9 A levelSubgroup
    supersingularCompatible hchar hcyclic hlevelOrder hinOrder hmod hsmall

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired

namespace SptCM.CM.Repaired

noncomputable section

open Polynomial
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
open SptCM.Repair

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
    (Dpoly : ActualClassPolynomialSpec C)

/-- I18--I19 with no independently chosen geometric specialization or point
compatibility datum.  Both are constructed from the one uniform E8
Hauptmodul good-reduction law. -/
theorem actual_common_root_oriented_specialization_of_goodReduction
    {L k Order IdealClass CMPoint Reduction D : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    [DivisionRing D] [Star D]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : E8IntegralClosureResidueSpecialization L k ℓ
      (SptCM.awaySixReduction ℓ h6))
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (hE8 : E8StandardCM CM)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (Hgood : E8ActualHauptmodulGoodReduction C F Sres CM E8Q)
    (hinert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
      CM.inertAt ℓ (E8Q.point r Q))
    (x : k)
    (hxA : aeval x (Dpoly.A.map (SptCM.awaySixReduction ℓ h6)) = 0)
    (hxB : aeval x (Dpoly.B.map (SptCM.awaySixReduction ℓ h6)) = 0) :
    Nonempty (Σ S : GeometricCMSpecialization CM,
      CollisionOrientedFormData CM S E8Q) := by
  exact Dpoly.actual_common_root_oriented_specialization
    h6 F Sres Hgood.coordinateSpecialization CM hE8
    (Hgood.pointReductionData hinert) E8Q
    (Hgood.pointCompatibility hinert) x hxA hxB

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired
