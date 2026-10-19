import blessed.SptCM.CM.Repaired.I16Reduction
import blessed.SptCM.Literature.Repair.UniformLedger

/-!
# Root factors after specialization of algebraic CM values

The roots of an actual class polynomial live in a number field (or an
integral extension), not in `ℤ[1/6]`.  This module proves the correct generic
algebraic bridge: once a coefficient descent is realized as a root product in
an extension ring and a compatible residue homomorphism is chosen, every
geometric root of the reduced coefficient polynomial is a specialized
algebraic root.
-/

namespace SptCM.CM.Repaired

noncomputable section

set_option maxHeartbeats 800000

open Polynomial

/-- Compatibility of an extension-ring specialization with coefficientwise
reduction of `ℤ[1/6]`. -/
def AwaySixResidueCompatibility
    {ℓ : ℕ} (h6 : IsUnit (6 : ZMod ℓ))
    {R k : Type*} [CommRing R] [Field k] [Algebra (ZMod ℓ) k]
    (incl : SptCM.AwaySix →+* R) (residue : R →+* k) : Prop :=
  residue.comp incl =
    (algebraMap (ZMod ℓ) k).comp (SptCM.awaySixReduction ℓ h6)

/-- A descended polynomial which becomes a finite root product in an
extension ring specializes to the product of the specialized roots. -/
theorem map_reducedPolynomial_eq_specialized_classPolynomial
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    {R k : Type*} [CommRing R] [Field k] [Algebra (ZMod ℓ) k]
    (incl : SptCM.AwaySix →+* R) (residue : R →+* k)
    (hcompat : AwaySixResidueCompatibility h6 incl residue)
    {ι : Type*} [Fintype ι] (roots : ι → R)
    (P : SptCM.AwaySix[X])
    (hP : P.map incl = SptCM.classPolynomial roots) :
    (P.map (SptCM.awaySixReduction ℓ h6)).map
        (algebraMap (ZMod ℓ) k) =
      SptCM.classPolynomial (fun i => residue (roots i)) := by
  classical
  rw [Polynomial.map_map, ← hcompat, ← Polynomial.map_map, hP]
  unfold SptCM.classPolynomial
  change (Polynomial.mapRingHom residue) (∏ i, (X - C (roots i))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- Hence a geometric root of the reduced coefficient polynomial is one of
those specialized algebraic roots. -/
theorem exists_specialized_root_of_reducedPolynomial_root
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ))
    {R k : Type*} [CommRing R] [Field k] [Algebra (ZMod ℓ) k]
    (incl : SptCM.AwaySix →+* R) (residue : R →+* k)
    (hcompat : AwaySixResidueCompatibility h6 incl residue)
    {ι : Type*} [Fintype ι] (roots : ι → R)
    (P : SptCM.AwaySix[X])
    (hP : P.map incl = SptCM.classPolynomial roots)
    (x : k)
    (hx : aeval x (P.map (SptCM.awaySixReduction ℓ h6)) = 0) :
    ∃ i : ι, x = residue (roots i) := by
  have hx' : Polynomial.eval x
      ((P.map (SptCM.awaySixReduction ℓ h6)).map
        (algebraMap (ZMod ℓ) k)) = 0 := by
    simpa [aeval_def] using hx
  rw [map_reducedPolynomial_eq_specialized_classPolynomial h6 incl
      residue hcompat roots P hP] at hx'
  apply (SptCM.aeval_classPolynomial_eq_zero_iff
    (fun i => residue (roots i)) x).1
  simpa [aeval_def] using hx'

/-- Coefficientwise maps carry a finite product of linear factors to
the product of the mapped roots. -/
theorem map_classPolynomial
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (f : R →+* S) (roots : ι → R) :
    (SptCM.classPolynomial roots).map f =
      SptCM.classPolynomial (fun i => f (roots i)) := by
  classical
  unfold SptCM.classPolynomial
  change (Polynomial.mapRingHom f) (∏ i, (X - Polynomial.C (roots i))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)

/-- The descended numerator, mapped back to the finite Galois class field,
is its product of algebraic CM root factors. -/
theorem mapA_eq_classField_numerator
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (F : C.FiniteGaloisRealization L) :
    D.A.map (algebraMap AwaySix L) = F.numeratorPolynomial := by
  apply Polynomial.map_injective F.embedding.toRingHom F.embedding_injective
  rw [Polynomial.map_map]
  have hcomp :
      F.embedding.toRingHom.comp (algebraMap AwaySix L) =
        awaySixToComplex := by
    ext a
    rw [awaySixToComplex_eq_algebraMap]
    exact (F.embedding.commutes (awaySixToRat a))
  rw [hcomp, D.mapA, F.map_numerator_eq_actual]
  rfl

/-- The analogous class-field factorization of the descended denominator. -/
theorem mapB_eq_classField_denominator
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (F : C.FiniteGaloisRealization L) :
    D.B.map (algebraMap AwaySix L) = F.denominatorPolynomial := by
  apply Polynomial.map_injective F.embedding.toRingHom F.embedding_injective
  rw [Polynomial.map_map]
  have hcomp :
      F.embedding.toRingHom.comp (algebraMap AwaySix L) =
        awaySixToComplex := by
    ext a
    rw [awaySixToComplex_eq_algebraMap]
    exact (F.embedding.commutes (awaySixToRat a))
  rw [hcomp, D.mapB, F.map_denominator_eq_actual]
  rfl

/-- The descended numerator, mapped into the integral closure, is its
product of integral algebraic CM root factors. -/
theorem mapA_eq_integralClosure_numerator
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (F : C.IntegralFiniteGaloisRealization L) :
    D.A.map (algebraMap AwaySix (integralClosure AwaySix L)) =
      SptCM.classPolynomial
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F) := by
  apply Polynomial.map_injective
    (integralClosure AwaySix L).subtype
    (by
      intro x y hxy
      exact Subtype.ext hxy)
  rw [Polynomial.map_map]
  have hcomp :
      (integralClosure AwaySix L).subtype.comp
          (algebraMap AwaySix (integralClosure AwaySix L)) =
        algebraMap AwaySix L := by
    ext a
    rfl
  rw [hcomp, D.mapA_eq_classField_numerator F.toFiniteGaloisRealization]
  have hm := map_classPolynomial (integralClosure AwaySix L).subtype
    (SptCM.RolenLiterature.Repair.integralNumeratorRoot F)
  rw [hm]
  rfl

/-- The analogous integral-closure factorization of the denominator. -/
theorem mapB_eq_integralClosure_denominator
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (F : C.IntegralFiniteGaloisRealization L) :
    D.B.map (algebraMap AwaySix (integralClosure AwaySix L)) =
      SptCM.classPolynomial
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F) := by
  apply Polynomial.map_injective
    (integralClosure AwaySix L).subtype
    (by
      intro x y hxy
      exact Subtype.ext hxy)
  rw [Polynomial.map_map]
  have hcomp :
      (integralClosure AwaySix L).subtype.comp
          (algebraMap AwaySix (integralClosure AwaySix L)) =
        algebraMap AwaySix L := by
    ext a
    rfl
  rw [hcomp, D.mapB_eq_classField_denominator F.toFiniteGaloisRealization]
  have hm := map_classPolynomial (integralClosure AwaySix L).subtype
    (SptCM.RolenLiterature.Repair.integralDenominatorRoot F)
  rw [hm]
  rfl

/-- I18 numerator factor theorem for the genuine descended numerator.  Every
geometric root after good-prime reduction is the residue of an *integral
closure* lift of an actual algebraic CM value. -/
theorem actualNumerator_root_factor
    {L k : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (S : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L k ℓ (SptCM.awaySixReduction ℓ h6))
    (x : k) (hx : aeval x (D.A.map
      (SptCM.awaySixReduction ℓ h6)) = 0) :
    ∃ i, x = S.residue
      (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i) :=
  exists_specialized_root_of_reducedPolynomial_root h6
    (algebraMap AwaySix (integralClosure AwaySix L)) S.residue (by
      exact S.compatible)
    (SptCM.RolenLiterature.Repair.integralNumeratorRoot F) D.A
    (D.mapA_eq_integralClosure_numerator F) x hx

/-- I18 denominator factor theorem through the integral closure. -/
theorem actualDenominator_root_factor
    {L k : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (S : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L k ℓ (SptCM.awaySixReduction ℓ h6))
    (x : k) (hx : aeval x (D.B.map
      (SptCM.awaySixReduction ℓ h6)) = 0) :
    ∃ i, x = S.residue
      (SptCM.RolenLiterature.Repair.integralDenominatorRoot F i) :=
  exists_specialized_root_of_reducedPolynomial_root h6
    (algebraMap AwaySix (integralClosure AwaySix L)) S.residue (by
      exact S.compatible)
    (SptCM.RolenLiterature.Repair.integralDenominatorRoot F) D.B
    (D.mapB_eq_integralClosure_denominator F) x hx

/-- A common geometric root yields factors from the two opposite orientation
families whose specialized level-structure points coincide.  Reduction is
performed only on the integral closure of `AwaySix` in the number field. -/
theorem actual_common_point_of_common_root
    {L k SpecialPoint : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra (ZMod ℓ) k]
    (h6 : IsUnit (6 : ZMod ℓ))
    (F : C.IntegralFiniteGaloisRealization L)
    (S : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L k ℓ (SptCM.awaySixReduction ℓ h6))
    (G : SptCM.RolenLiterature.E8IntegralCoordinateSpecialization
      (C.orientation1.Index ⊕ C.orientation11.Index)
      (C.orientation5.Index ⊕ C.orientation7.Index) k SpecialPoint
      (fun i => S.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i))
      (fun j => S.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j)))
    (x : k)
    (hxA : aeval x (D.A.map (SptCM.awaySixReduction ℓ h6)) = 0)
    (hxB : aeval x (D.B.map (SptCM.awaySixReduction ℓ h6)) = 0) :
    ∃ i j,
      x = S.residue
        (SptCM.RolenLiterature.Repair.integralNumeratorRoot F i) ∧
      x = S.residue
        (SptCM.RolenLiterature.Repair.integralDenominatorRoot F j) ∧
      G.pointX i = G.pointY j := by
  obtain ⟨i, hi⟩ := D.actualNumerator_root_factor h6 F S x hxA
  obtain ⟨j, hj⟩ := D.actualDenominator_root_factor h6 F S x hxB
  refine ⟨i, j, hi, hj, G.coordinate_injective ?_⟩
  rw [G.realizesX, G.realizesY, ← hi, ← hj]

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired
