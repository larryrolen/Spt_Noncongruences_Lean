module

public import blessed.SptCM.CM.Repaired.I18RootSpecialization
public import blessed.SptCM.Quaternion.Repaired.CommonRootSeparation

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# From an actual common class-polynomial root to a CM specialization

This module connects the coefficient/root calculation of I18 with the
standard E8 good-reduction and Deuring interface.  The bridge below records
only which characteristic-zero CM points underlie each of the two finite
families and how their reductions agree with the specialized modular-curve
points.  It contains no collision or supersingularity conclusion.
-/

namespace SptCM.CM.Repaired

noncomputable section

open Polynomial
open SptCM.RolenLiterature

/-- Interpretation of the two specialized class-field root families as
reductions of the corresponding characteristic-zero CM points.  Inertness
is recorded pointwise because `CMTheoryModel.inertAt` is an abstract
interpretation predicate; Deuring's supersingularity conclusion is not a
field. -/
structure ActualCMPointReductionData
    {I J Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism)
    (ℓ : ℕ)
    (pointX : I → Reduction) (pointY : J → Reduction) where
  numeratorPoint : I → CMPoint
  denominatorPoint : J → CMPoint
  realizesNumerator : ∀ i, CM.reduction (numeratorPoint i) = pointX i
  realizesDenominator : ∀ j, CM.reduction (denominatorPoint j) = pointY j
  numeratorInert : ∀ i, CM.inertAt ℓ (numeratorPoint i)
  denominatorInert : ∀ j, CM.inertAt ℓ (denominatorPoint j)

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)

/-- I18: a common root of the two genuine coefficientwise reductions gives
two actual CM points with the same reduction; the general E8 theorems then
give potential good reduction, supersingularity, and injectivity of both CM
specializations.  None of these conclusions is assumed in the reduction
interpretation datum. -/
theorem actual_common_root_specialization
    {L k Order IdealClass CMPoint Reduction Endomorphism : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (S : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L k ℓ (SptCM.awaySixReduction ℓ h6))
    (G : E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) k Reduction
      (fun i => S.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i))
      (fun j => S.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j)))
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism)
    (hE8 : E8StandardCM CM)
    (R : ActualCMPointReductionData CM ℓ G.pointX G.pointY)
    (x : k)
    (hxA : aeval x (D.A.map (SptCM.awaySixReduction ℓ h6)) = 0)
    (hxB : aeval x (D.B.map (SptCM.awaySixReduction ℓ h6)) = 0) :
    Nonempty (SptCM.Repair.GeometricCMSpecialization CM) := by
  obtain ⟨i, j, _hi, _hj, hp⟩ :=
    D.actual_common_point_of_common_root h6 F S G x hxA hxB
  refine ⟨{
    numeratorPoint := R.numeratorPoint i
    denominatorPoint := R.denominatorPoint j
    sameReduction := ?_
    numeratorGoodReduction := hE8.2.1 _
    denominatorGoodReduction := hE8.2.1 _
    supersingular := hE8.2.2.1 ℓ _ (R.numeratorInert i)
    numeratorActionInjective := hE8.2.2.2 _
    denominatorActionInjective := hE8.2.2.2 _ }⟩
  rw [R.realizesNumerator, R.realizesDenominator]
  exact hp

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired
