import blessed.SptCM.Repair.I12WronskianZero
import blessed.SptCM.Repair.WronskianAssembly
import blessed.SptCM.Quaternion.Repaired.I19ActualAdapter
import blessed.SptCM.Quaternion.Repaired.ActualPointConstruction
import blessed.SptCM.Repair.FinalAssembly

/-!
# Genuine actual-class-polynomial Wronskian contradiction

This module joins the analytic vanishing theorem to the indexed E8--E9
separation theorem and hence to the algebraic nonvanishing theorem.  In
particular, neither a Wronskian conclusion nor polynomial separation is an
input.

The theorem is deliberately pointwise.  Promoting it to the uniform cutoff
statement requires uniform, discriminant-indexed instances of every
source-facing datum displayed in its signature (most notably the integral
Galois realization, integral-closure specialization, identification of the
analytic and quadratic-form CM points, and the normalized Borcherds quotient).
That uniform literature ledger is the remaining family-level interface needed
before `large_exclusion_of_wronskian_contradiction` can be applied.
-/

namespace SptCM.Repair

noncomputable section

open Polynomial
open SptCM.RolenLiterature
open SptCM.Analytic
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

/-- The small-discriminant inequality in the final contradiction is already
strong enough to put the prime away from two and three. -/
lemma five_le_of_mod_twentyFour_and_collision_bound
    {n ℓ : ℕ} (hmod : n % 24 = 23)
    (hsmall : (n + 1) ^ 2 < 24 * ℓ) : 5 ≤ ℓ := by
  have hn : 23 ≤ n := by
    rw [← hmod]
    exact Nat.mod_le n 24
  nlinarith

/-- At one admissible discriminant, the genuine analytic Wronskian vanishing
and genuine E8--E9 CM separation contradict each other.  Every hypothesis is
upstream model/comparison data consumed by the existing constructions; no
hypothesis asserts vanishing, nonvanishing, coprimality, collision, a volume
inequality, or exclusion. -/
theorem actualClassPolynomials_wronskian_contradiction
    {Form Product : Type*} [SMul ℂ Form]
    {n h ℓ : ℕ} [Fact ℓ.Prime]
    {C : ActualOrientedCMCoordinates n h}
    (Dpoly : ActualClassPolynomialSpec C)
    (E : EtaJGeneratorBasis Form)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid)
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hadm : SptCM.Admissible ℓ n)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hquotient :
      actualClassPolynomialLaurentQuotient Dpoly
          actualRationalHauptmodulLaurent =
        actualBorcherdsEulerQuotient
          (auxiliaryFourComponentInput E ((n + 1) / 24)
            (aCoeff (n : ℤ))))
    {L Order IdealClass CMPoint Reduction Dq Subgroup Lattice : Type*}
    [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L]
    [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq]
    (F : C.IntegralFiniteGaloisRealization L)
    (Sres : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
      L (AlgebraicClosure (ZMod ℓ)) ℓ
      (SptCM.awaySixReduction ℓ
        (SptCM.six_isUnit_zmod_of_prime_five_le
          hcanonical.prime hcanonical.five_le)))
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
    (Rred : ActualCMPointReductionData CM ℓ G.pointX G.pointY)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (H : ActualOrientedPointCompatibility C CM Rred E8Q)
    (EC : EichlerCovolumeModel Reduction Subgroup (Subring Dq) Lattice Dq)
    (hE9 : E9ArpinGorenLauter EC)
    (Arith : EichlerLatticeArithmetic EC)
    (levelSubgroup : GeometricCMSpecialization CM → Subgroup)
    (supersingularCompatible : ∀ P,
      CM.supersingular P → EC.supersingular P)
    (hchar : ∀ S : GeometricCMSpecialization CM,
      Arith.characteristic (CM.reduction S.numeratorPoint) = ℓ)
    (hcyclic : ∀ S : GeometricCMSpecialization CM,
      EC.cyclicOfOrderSix (levelSubgroup S))
    (hlevelOrder : ∀ S : GeometricCMSpecialization CM,
      E8Q.levelOrder =
        EC.preservingOrder (CM.reduction S.numeratorPoint) (levelSubgroup S))
    (hinOrder : ∀ O x, Arith.inOrder O x ↔ x ∈ O)
    (hsmall : (n + 1) ^ 2 < 24 * ℓ)
    (hdegreePos : 0 < 2 * h)
    (hdegreeLt : 2 * h < ℓ) :
    False := by
  let h6 : IsUnit (6 : ZMod ℓ) :=
    SptCM.six_isUnit_zmod_of_prime_five_le
      hcanonical.prime hcanonical.five_le
  have hcop : IsCoprime
      (Dpoly.A.map (SptCM.awaySixReduction ℓ h6))
      (Dpoly.B.map (SptCM.awaySixReduction ℓ h6)) :=
    Dpoly.actualClassPolynomials_isCoprime_of_indexed_E8_E9
      h6 F Sres G CM hE8 Rred E8Q H EC hE9 Arith levelSubgroup
      supersingularCompatible hchar hcyclic hlevelOrder hinOrder hadm.2.1 hsmall
  have hne : SptCM.wronskianObstruction
      (Dpoly.actualReducedClassPolynomials ℓ h6).1
      (Dpoly.actualReducedClassPolynomials ℓ h6).2 ≠ 0 :=
    actualClassPolynomials_wronskian_ne_zero Dpoly h6 hcop
      hdegreePos hdegreeLt
  have heq : SptCM.wronskianObstruction
      (Dpoly.actualReducedClassPolynomials ℓ h6).1
      (Dpoly.actualReducedClassPolynomials ℓ h6).2 = 0 := by
    simpa only [h6] using
      actualClassPolynomials_wronskian_eq_zero Dpoly E Grid Mult
        hcanonical hadm hAK hquotient
  exact hne heq


/-- All E8--E9 application data at one prime and one eligible
discriminant.  The carrier fields are local because both the CM class field
and the supersingular quaternion algebra vary with the application.  Every
mathematical field is upstream data: this structure contains no polynomial
coprimality, common-root collision, Wronskian statement, volume inequality,
or prime-exclusion conclusion. -/
structure ActualCMApplicationPackage
    {n h ℓ : ℕ} [Fact ℓ.Prime]
    (C : ActualOrientedCMCoordinates n h)
    (h6 : IsUnit (6 : ZMod ℓ)) where
  L : Type
  Order : Type
  IdealClass : Type
  CMPoint : Type
  Reduction : Type
  Dq : Type
  Subgroup : Type
  Lattice : Type
  [fieldL : Field L]
  [algebraL : Algebra ℚ L]
  [finiteDimensionalL : FiniteDimensional ℚ L]
  [isGaloisL : IsGalois ℚ L]
  [divisionRingDq : DivisionRing Dq]
  [starDq : Star Dq]
  [algebraDq : Algebra ℚ Dq]
  F : C.IntegralFiniteGaloisRealization L
  Sres : SptCM.RolenLiterature.Repair.E8IntegralClosureResidueSpecialization
    L (AlgebraicClosure (ZMod ℓ)) ℓ (SptCM.awaySixReduction ℓ h6)
  CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq
  hE8 : E8StandardCM CM
  E8Q : E8OrientedQuadraticSpecialization n CM
  Hgood : E8ActualHauptmodulGoodReduction C F Sres CM E8Q
  rawPointInert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r),
    CM.inertAt ℓ (E8Q.point r Q)
  EC : EichlerCovolumeModel Reduction Subgroup (Subring Dq) Lattice Dq
  hE9 : E9ArpinGorenLauter EC
  Arith : EichlerLatticeArithmetic EC
  levelSubgroup : GeometricCMSpecialization CM → Subgroup
  supersingularCompatible : ∀ P, CM.supersingular P → EC.supersingular P
  hchar : ∀ S : GeometricCMSpecialization CM,
    Arith.characteristic (CM.reduction S.numeratorPoint) = ℓ
  hcyclic : ∀ S : GeometricCMSpecialization CM,
    EC.cyclicOfOrderSix (levelSubgroup S)
  hlevelOrder : ∀ S : GeometricCMSpecialization CM,
    E8Q.levelOrder =
      EC.preservingOrder (CM.reduction S.numeratorPoint) (levelSubgroup S)
  hinOrder : ∀ O x, Arith.inOrder O x ↔ x ∈ O

/-- Family-level large exclusion with the geometric E8 comparison data
constructed internally.  Every discriminant-indexed object is requested only
for squarefree `n ≡ 23 (mod 24)`, and the E8--E9 application package is local
to the particular `(ℓ,n)` selected by E10.  Thus this statement neither asks
for impossible coordinates at `n = 0` nor for one finite class field or one
quaternion algebra to serve all discriminants and primes.

The package exposes only source-facing Hauptmodul good reduction, raw-point
inertness, and the E8/E9 arithmetic models.  Coordinate specializations,
reduction records, oriented point identifications, coprimality, Wronskian
conclusions, collisions, volume bounds, and exclusion are constructed rather
than assumed. -/
theorem large_exclusion_of_uniform_actual_goodReduction
    {Form Product : Type*} [SMul ℂ Form]
    (hE10 : E10TrevinoCorrected)
    (Cfam : ∀ (n : ℕ), Squarefree n → n % 24 = 23 →
      ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n))
    (Dfam : ∀ (n : ℕ) (hs : Squarefree n) (hm : n % 24 = 23),
      ActualClassPolynomialSpec (Cfam n hs hm))
    (E : EtaJGeneratorBasis Form)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid)
    (hAK : ∀ ℓ [Fact ℓ.Prime], 5 ≤ ℓ →
      AhlgrenKimThetaCycleFromUInput ℓ)
    (hquotient : ∀ (n : ℕ) (hs : Squarefree n) (hm : n % 24 = 23),
      actualClassPolynomialLaurentQuotient (Dfam n hs hm)
          actualRationalHauptmodulLaurent =
        actualBorcherdsEulerQuotient
          (auxiliaryFourComponentInput E ((n + 1) / 24)
            (aCoeff (n : ℤ))))
    (Appfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h5 : 5 ≤ ℓ)
      (n : ℕ) (hs : Squarefree n) (hm : n % 24 = 23)
      (hinert : legendreSym ℓ (-(n : ℤ)) = -1),
      ActualCMApplicationPackage (Cfam n hs hm)
        (SptCM.six_isUnit_zmod_of_prime_five_le
          (Fact.out : ℓ.Prime) h5))
    (ℓ : ℕ) (hprime : ℓ.Prime) (hlarge : SptCM.cutoff ≤ ℓ) :
    ¬ SptCM.CanonicalCongruencePrime ℓ := by
  letI : Fact ℓ.Prime := ⟨hprime⟩
  obtain ⟨n, hsquarefree, hmod, hinert, hsmall, hdegreePos, hdegreeLt⟩ :=
    small_n_of_E10 hE10 ℓ hlarge
  intro hcanonical
  have hadm : SptCM.Admissible ℓ n := by
    refine ⟨hsquarefree, hmod, ?_⟩
    have hi := (legendreSym.eq_neg_one_iff ℓ).1 hinert
    simpa using hi
  have h5 : 5 ≤ ℓ := hcanonical.five_le
  have hz := actualClassPolynomials_wronskian_eq_zero
    (Dfam n hsquarefree hmod) E Grid Mult hcanonical hadm (hAK ℓ h5)
      (hquotient n hsquarefree hmod)
  let h6 : IsUnit (6 : ZMod ℓ) :=
    SptCM.six_isUnit_zmod_of_prime_five_le hprime h5
  let P := Appfam ℓ h5 n hsquarefree hmod hinert
  letI : Field P.L := P.fieldL
  letI : Algebra ℚ P.L := P.algebraL
  letI : FiniteDimensional ℚ P.L := P.finiteDimensionalL
  letI : IsGalois ℚ P.L := P.isGaloisL
  letI : DivisionRing P.Dq := P.divisionRingDq
  letI : Star P.Dq := P.starDq
  letI : Algebra ℚ P.Dq := P.algebraDq
  have hcop :=
    (Dfam n hsquarefree hmod).actualClassPolynomials_isCoprime_of_goodReduction_E8_E9
      h6 P.F P.Sres P.CM P.hE8 P.E8Q P.Hgood P.rawPointInert
      P.EC P.hE9 P.Arith P.levelSubgroup P.supersingularCompatible
      P.hchar P.hcyclic P.hlevelOrder P.hinOrder hmod hsmall
  have hnz := actualClassPolynomials_wronskian_ne_zero
    (Dfam n hsquarefree hmod) h6 hcop hdegreePos hdegreeLt
  exact hnz (by simpa [h6] using hz)

end

end SptCM.Repair
