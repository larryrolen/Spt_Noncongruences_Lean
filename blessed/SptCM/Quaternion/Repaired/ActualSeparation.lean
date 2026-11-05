module

public import blessed.SptCM.CM.Repaired.I18CommonRoot
public import blessed.SptCM.Quaternion.Repaired.I20Covolume
public import blessed.SptCM.Arithmetic.SmallDiscriminant

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Separation of the genuine reduced class polynomials

This file composes I18--I20 for the actual descended polynomials.  All
remaining parameters are transparent comparison data between the standard
E8 reduction model and the standard E9 preserving-order/covolume model; no
parameter asserts coprimality, noncommutation, a volume bound, or a
Wronskian conclusion.
-/

namespace SptCM.Repair

noncomputable section

open Polynomial
open SptCM.RolenLiterature
open SptCM.CM.Repaired

/-- The actual I18--I20 separation theorem.  A hypothetical common geometric
root constructs the common supersingular specialization, the two genuine
quadratic-order actions, and their level-six volume inequality.  The
congruence `n ≡ 23 (mod 24)` identifies the common norm with `(n+1)/4`, and
the strict collision bound gives the contradiction. -/
theorem actualClassPolynomials_isCoprime_of_E8_E9
    {n h ℓ : ℕ} [Fact ℓ.Prime]
    {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)
    (h6 : IsUnit (6 : ZMod ℓ))
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ h6))
    {OrderCM IdealClass CMPoint Reduction Dq Subgroup Lattice : Type*}
    [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
    (G : E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index)
      (AlgebraicClosure (ZMod ℓ)) Reduction
      (fun i => Sres.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i))
      (fun j => Sres.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j)))
    (CM : CMTheoryModel OrderCM IdealClass CMPoint Reduction Dq)
    (hE8 : E8StandardCM CM)
    (R : ActualCMPointReductionData CM ℓ G.pointX G.pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (forms : ∀ S : GeometricCMSpecialization CM,
      CollisionOrientedFormData CM S E8Q)
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
    IsCoprime (D.A.map (SptCM.awaySixReduction ℓ h6))
      (D.B.map (SptCM.awaySixReduction ℓ h6)) := by
  by_contra hnot
  have hroot : ∃ x : AlgebraicClosure (ZMod ℓ),
      aeval x (D.A.map (SptCM.awaySixReduction ℓ h6)) = 0 ∧
      aeval x (D.B.map (SptCM.awaySixReduction ℓ h6)) = 0 := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))] at hnot
    push Not at hnot
    exact hnot
  obtain ⟨x, hxA, hxB⟩ := hroot
  obtain ⟨S⟩ := D.actual_common_root_specialization
    h6 F Sres G CM hE8 R x hxA hxB
  have hvolume : 6 * ℓ ≤ 4 * ((n + 1) / 4) ^ 2 :=
    A.actual_specialized_actions_volume_of_E8_E9 CM S E8Q (forms S)
      EC hE9 (CM.reduction S.numeratorPoint) (levelSubgroup S) rfl
      supersingularCompatible (hchar S) (hcyclic S) (hlevelOrder S) hinOrder
  have hnorm : n + 1 = 4 * ((n + 1) / 4) := by omega
  exact SptCM.collision_impossible_of_volume hnorm hvolume hsmall

end

end SptCM.Repair
