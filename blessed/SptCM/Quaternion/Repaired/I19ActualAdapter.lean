import blessed.SptCM.CM.Repaired.I18CommonRoot
import blessed.SptCM.Quaternion.Repaired.CommonRootSeparation
import blessed.SptCM.Quaternion.Repaired.I20Covolume
import blessed.SptCM.Arithmetic.SmallDiscriminant

/-!
# Actual-index adapter for the I19 oriented specialization

A common root identifies particular indices in the four genuine oriented CM
families.  This module retains those indices while applying E8, and derives
the `CollisionOrientedFormData` consumed by the quaternionic argument.

The only comparison datum below says that a CM point indexed by one of the
actual finite class enumerations is the E8 point attached to a representative
of that very quotient class.  It contains no trace, norm, scalar,
noncommutation, volume, or polynomial-separation conclusion.
-/

namespace SptCM.CM.Repaired

noncomputable section

open Polynomial
open SptCM.RolenLiterature
open SptCM.Repair

/-- Choose a raw form representing an actual oriented quotient class.  The
choice is internal; no representative is part of the E8 assumptions. -/
noncomputable def rawRepresentative {n r : ℕ}
    (q : SptCM.orientedForms n r) : SptCM.RawOrientedForm n r :=
  Quotient.out q

@[simp] theorem mk_rawRepresentative {n r : ℕ}
    (q : SptCM.orientedForms n r) :
    Quotient.mk'' (rawRepresentative q) = q :=
  Quotient.out_eq q

/-- Source-faithful comparison between the four actual quotient-class
enumerations and the raw-form presentation used by the standard E8
specialization theorem.  The quotient equalities prevent an unrelated raw
form with the same orientation from being substituted for the indexed CM
point. -/
structure ActualOrientedPointCompatibility
    {n h ℓ : ℕ} (C : ActualOrientedCMCoordinates n h)
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    {pointX : (C.orientation1.Index ⊕ C.orientation11.Index) → Reduction}
    {pointY : (C.orientation5.Index ⊕ C.orientation7.Index) → Reduction}
    (R : ActualCMPointReductionData CM ℓ pointX pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM) where
  numeratorOne : ∀ i : C.orientation1.Index,
    ∃ Q : SptCM.RawOrientedForm n 1,
      Quotient.mk'' Q = C.orientation1.classes i ∧
      R.numeratorPoint (.inl i) = E8Q.point 1 Q
  numeratorEleven : ∀ i : C.orientation11.Index,
    ∃ Q : SptCM.RawOrientedForm n 11,
      Quotient.mk'' Q = C.orientation11.classes i ∧
      R.numeratorPoint (.inr i) = E8Q.point 11 Q
  denominatorFive : ∀ i : C.orientation5.Index,
    ∃ Q : SptCM.RawOrientedForm n 5,
      Quotient.mk'' Q = C.orientation5.classes i ∧
      R.denominatorPoint (.inl i) = E8Q.point 5 Q
  denominatorSeven : ∀ i : C.orientation7.Index,
    ∃ Q : SptCM.RawOrientedForm n 7,
      Quotient.mk'' Q = C.orientation7.classes i ∧
      R.denominatorPoint (.inr i) = E8Q.point 7 Q

/-- The irreducible point-identification content of the comparison, after
raw representatives have been chosen internally by `rawRepresentative`.
This deliberately contains only identities of two presentations of the same
CM point. -/
structure ActualOrientedPointIdentification
    {n h ℓ : ℕ} (C : ActualOrientedCMCoordinates n h)
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    {pointX : (C.orientation1.Index ⊕ C.orientation11.Index) → Reduction}
    {pointY : (C.orientation5.Index ⊕ C.orientation7.Index) → Reduction}
    (R : ActualCMPointReductionData CM ℓ pointX pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM) where
  numeratorOne : ∀ i : C.orientation1.Index,
    R.numeratorPoint (.inl i) =
      E8Q.point 1 (rawRepresentative (C.orientation1.classes i))
  numeratorEleven : ∀ i : C.orientation11.Index,
    R.numeratorPoint (.inr i) =
      E8Q.point 11 (rawRepresentative (C.orientation11.classes i))
  denominatorFive : ∀ i : C.orientation5.Index,
    R.denominatorPoint (.inl i) =
      E8Q.point 5 (rawRepresentative (C.orientation5.classes i))
  denominatorSeven : ∀ i : C.orientation7.Index,
    R.denominatorPoint (.inr i) =
      E8Q.point 7 (rawRepresentative (C.orientation7.classes i))

/-- Once the two point presentations have been identified, all choices and
quotient-class checks required by the collision adapter are internal. -/
theorem ActualOrientedPointCompatibility.ofIdentification
    {n h ℓ : ℕ} {C : ActualOrientedCMCoordinates n h}
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    {CM : CMTheoryModel Order IdealClass CMPoint Reduction D}
    {pointX : (C.orientation1.Index ⊕ C.orientation11.Index) → Reduction}
    {pointY : (C.orientation5.Index ⊕ C.orientation7.Index) → Reduction}
    {R : ActualCMPointReductionData CM ℓ pointX pointY}
    {E8Q : E8OrientedQuadraticSpecialization n CM}
    (H : ActualOrientedPointIdentification C CM R E8Q) :
    ActualOrientedPointCompatibility C CM R E8Q where
  numeratorOne i :=
    ⟨rawRepresentative (C.orientation1.classes i),
      mk_rawRepresentative _, H.numeratorOne i⟩
  numeratorEleven i :=
    ⟨rawRepresentative (C.orientation11.classes i),
      mk_rawRepresentative _, H.numeratorEleven i⟩
  denominatorFive i :=
    ⟨rawRepresentative (C.orientation5.classes i),
      mk_rawRepresentative _, H.denominatorFive i⟩
  denominatorSeven i :=
    ⟨rawRepresentative (C.orientation7.classes i),
      mk_rawRepresentative _, H.denominatorSeven i⟩

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
    (Dpoly : ActualClassPolynomialSpec C)

/-- I18--I19 adapter for the genuine class-polynomial indices.  From an
actual common root it produces a specialized CM pair together with raw forms
representing the *same indexed quotient classes*.  Potential good reduction,
supersingularity, injectivity, and all action data are conclusions of the
standard E8 inputs rather than fields of the comparison datum. -/
theorem actual_common_root_oriented_specialization
    {L k Order IdealClass CMPoint Reduction D : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    [DivisionRing D] [Star D]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L k ℓ (SptCM.awaySixReduction ℓ h6))
    (G : E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) k Reduction
      (fun i => Sres.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i))
      (fun j => Sres.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j)))
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (hE8 : E8StandardCM CM)
    (R : ActualCMPointReductionData CM ℓ G.pointX G.pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (H : ActualOrientedPointCompatibility C CM R E8Q)
    (x : k)
    (hxA : aeval x (Dpoly.A.map (SptCM.awaySixReduction ℓ h6)) = 0)
    (hxB : aeval x (Dpoly.B.map (SptCM.awaySixReduction ℓ h6)) = 0) :
    Nonempty (Σ S : GeometricCMSpecialization CM,
      CollisionOrientedFormData CM S E8Q) := by
  obtain ⟨i, j, _hi, _hj, hp⟩ :=
    Dpoly.actual_common_point_of_common_root h6 F Sres G x hxA hxB
  let S : GeometricCMSpecialization CM :=
    { numeratorPoint := R.numeratorPoint i
      denominatorPoint := R.denominatorPoint j
      sameReduction := by
        rw [R.realizesNumerator, R.realizesDenominator]
        exact hp
      numeratorGoodReduction := hE8.2.1 _
      denominatorGoodReduction := hE8.2.1 _
      supersingular := hE8.2.2.1 ℓ _ (R.numeratorInert i)
      numeratorActionInjective := hE8.2.2.2 _
      denominatorActionInjective := hE8.2.2.2 _ }
  rcases i with i | i <;> rcases j with j | j
  · obtain ⟨Qi, _hQi, hiPoint⟩ := H.numeratorOne i
    obtain ⟨Qj, _hQj, hjPoint⟩ := H.denominatorFive j
    exact ⟨⟨S, {
      numeratorResidue := 1
      denominatorResidue := 5
      numeratorOrientation := Or.inl rfl
      denominatorOrientation := Or.inl rfl
      numeratorForm := Qi
      denominatorForm := Qj
      numeratorPoint := hiPoint
      denominatorPoint := hjPoint }⟩⟩
  · obtain ⟨Qi, _hQi, hiPoint⟩ := H.numeratorOne i
    obtain ⟨Qj, _hQj, hjPoint⟩ := H.denominatorSeven j
    exact ⟨⟨S, {
      numeratorResidue := 1
      denominatorResidue := 7
      numeratorOrientation := Or.inl rfl
      denominatorOrientation := Or.inr rfl
      numeratorForm := Qi
      denominatorForm := Qj
      numeratorPoint := hiPoint
      denominatorPoint := hjPoint }⟩⟩
  · obtain ⟨Qi, _hQi, hiPoint⟩ := H.numeratorEleven i
    obtain ⟨Qj, _hQj, hjPoint⟩ := H.denominatorFive j
    exact ⟨⟨S, {
      numeratorResidue := 11
      denominatorResidue := 5
      numeratorOrientation := Or.inr rfl
      denominatorOrientation := Or.inl rfl
      numeratorForm := Qi
      denominatorForm := Qj
      numeratorPoint := hiPoint
      denominatorPoint := hjPoint }⟩⟩
  · obtain ⟨Qi, _hQi, hiPoint⟩ := H.numeratorEleven i
    obtain ⟨Qj, _hQj, hjPoint⟩ := H.denominatorSeven j
    exact ⟨⟨S, {
      numeratorResidue := 11
      denominatorResidue := 7
      numeratorOrientation := Or.inr rfl
      denominatorOrientation := Or.inr rfl
      numeratorForm := Qi
      denominatorForm := Qj
      numeratorPoint := hiPoint
      denominatorPoint := hjPoint }⟩⟩

/-- Separation with the actual-index adapter.  Unlike the older assembly,
this theorem does not request `CollisionOrientedFormData` for every abstract
specialization.  It constructs the one specialization that arises from a
common root, using only the point/form comparison `H`. -/
theorem actualClassPolynomials_isCoprime_of_indexed_E8_E9
    {L Order IdealClass CMPoint Reduction Dq Subgroup Lattice : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    {ℓ : ℕ} [Fact ℓ.Prime]
    [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ h6))
    (G : E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index)
      (AlgebraicClosure (ZMod ℓ)) Reduction
      (fun i => Sres.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i))
      (fun j => Sres.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j)))
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq)
    (hE8 : E8StandardCM CM)
    (R : ActualCMPointReductionData CM ℓ G.pointX G.pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (H : ActualOrientedPointCompatibility C CM R E8Q)
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
  by_contra hnot
  have hroot : ∃ x : AlgebraicClosure (ZMod ℓ),
      aeval x (Dpoly.A.map (SptCM.awaySixReduction ℓ h6)) = 0 ∧
      aeval x (Dpoly.B.map (SptCM.awaySixReduction ℓ h6)) = 0 := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))] at hnot
    push Not at hnot
    exact hnot
  obtain ⟨x, hxA, hxB⟩ := hroot
  obtain ⟨S, forms⟩ :=
    Dpoly.actual_common_root_oriented_specialization
      h6 F Sres G CM hE8 R E8Q H x hxA hxB
  have hvolume : 6 * ℓ ≤ 4 * ((n + 1) / 4) ^ 2 :=
    A.actual_specialized_actions_volume_of_E8_E9 CM S E8Q forms
      EC hE9 (CM.reduction S.numeratorPoint) (levelSubgroup S) rfl
      supersingularCompatible (hchar S) (hcyclic S) (hlevelOrder S) hinOrder
  have hnorm : n + 1 = 4 * ((n + 1) / 4) := by omega
  exact SptCM.collision_impossible_of_volume hnorm hvolume hsmall

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired
