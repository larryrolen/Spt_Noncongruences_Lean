import blessed.SptCM.Analytic.Repaired.UniformNormalizedProduct
import blessed.SptCM.Repair.ActualWronskianContradiction
import blessed.SptCM.Literature.Repair.PublicLedger
import blessed.SptCM.Repair.FinalAssembly

/-!
# Large-prime exclusion from source-facing analytic data

This wrapper removes the normalized quotient from the hypotheses of the
large-exclusion theorem.  It is derived uniformly from the E3--E6 analytic
package before invoking the Wronskian contradiction.
-/

namespace SptCM.Repair

noncomputable section

open SptCM.RolenLiterature
open SptCM.Analytic
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

/-- Large-prime exclusion in which the normalized I12 product is a theorem,
not an input.  The remaining `Appfam` is exactly the discriminant- and
prime-dependent E8--E9 application package used by the algebraic separation
half of the proof. -/
theorem large_exclusion_of_uniform_actual_analytic_goodReduction
    {Form Product Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (hE10 : E10TrevinoCorrected)
    (Cfam : ∀ (n : ℕ), Squarefree n → n % 24 = 23 →
      ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n))
    (Dfam : ∀ (n : ℕ) (hs : Squarefree n) (hm : n % 24 = 23),
      ActualClassPolynomialSpec (Cfam n hs hm))
    (E : EtaJGeneratorBasis Form)
    (P : UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid)
    (hAK : ∀ ℓ [Fact ℓ.Prime], 5 ≤ ℓ → AhlgrenKimThetaCycleFromUInput ℓ)
    (Appfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h5 : 5 ≤ ℓ)
      (n : ℕ) (hs : Squarefree n) (hm : n % 24 = 23)
      (hinert : legendreSym ℓ (-(n : ℤ)) = -1),
      ActualCMApplicationPackage (Cfam n hs hm)
        (SptCM.six_isUnit_zmod_of_prime_five_le
          (Fact.out : ℓ.Prime) h5))
    (ℓ : ℕ) (hprime : ℓ.Prime) (hlarge : SptCM.cutoff ≤ ℓ) :
    ¬ SptCM.CanonicalCongruencePrime ℓ := by
  apply large_exclusion_of_uniform_actual_goodReduction hE10 Cfam Dfam E
    Grid Mult hAK
  · intro n hs hm
    exact P.normalizedIdentity hm (Dfam n hs hm)
  · exact Appfam
  · exact hprime
  · exact hlarge

/-- Large-prime exclusion with a single local dependent CM package.

After E10 selects the discriminant, `lit` supplies one actual coordinate
family together with its E8--E9 application package.  The class polynomials
are descended from the integral realization in that very package.  Hence the
analytic normalized identity and the algebraic separation theorem concern
definitionally the same coordinates and polynomials; no independent
`Cfam`/`Dfam` choices occur in this theorem. -/
theorem large_exclusion_of_uniform_literature
    {Form Product Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (lit : SptCM.RolenLiterature.Repair.UniformRolenLiterature)
    (E : EtaJGeneratorBasis Form)
    (Analytic :
      UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid)
    (ℓ : ℕ) (hprime : ℓ.Prime) (hlarge : SptCM.cutoff ≤ ℓ) :
    ¬ SptCM.CanonicalCongruencePrime ℓ := by
  letI : Fact ℓ.Prime := ⟨hprime⟩
  obtain ⟨n, hsquarefree, hmod, hinert, hsmall, hdegreePos, hdegreeLt⟩ :=
    small_n_of_E10 lit.e10 ℓ hlarge
  intro hcanonical
  have hadm : SptCM.Admissible ℓ n := by
    refine ⟨hsquarefree, hmod, ?_⟩
    have hi := (legendreSym.eq_neg_one_iff ℓ).1 hinert
    simpa using hi
  have h5 : 5 ≤ ℓ := hcanonical.five_le
  let h6 : IsUnit (6 : ZMod ℓ) :=
    SptCM.six_isUnit_zmod_of_prime_five_le hprime h5
  let Q := Classical.choice
    (lit.actualCMPolynomialApplicationPackage h5 hsquarefree hmod hinert)
  let C := Q.1
  let D := Q.2.1
  let A := Q.2.2
  have hz := actualClassPolynomials_wronskian_eq_zero
    D E Grid Mult hcanonical hadm (lit.arithmetic.e2ThetaCycle ℓ h5)
      (Analytic.normalizedIdentity hmod D)
  letI : Field A.L := A.fieldL
  letI : Algebra ℚ A.L := A.algebraL
  letI : FiniteDimensional ℚ A.L := A.finiteDimensionalL
  letI : IsGalois ℚ A.L := A.isGaloisL
  letI : DivisionRing A.Dq := A.divisionRingDq
  letI : Star A.Dq := A.starDq
  letI : Algebra ℚ A.Dq := A.algebraDq
  have hcop :=
    D.actualClassPolynomials_isCoprime_of_goodReduction_E8_E9
      h6 A.F A.Sres A.CM A.hE8 A.E8Q A.Hgood A.rawPointInert
      A.EC A.hE9 A.Arith A.levelSubgroup A.supersingularCompatible
      A.hchar A.hcyclic A.hlevelOrder A.hinOrder hmod hsmall
  have hnz := actualClassPolynomials_wronskian_ne_zero
    D h6 hcop hdegreePos hdegreeLt
  exact hnz (by simpa [h6] using hz)

/-- Rolen's classification assembled solely from the source-facing uniform
literature ledger and the independently supplied E3--E6 analytic models.
No normalized product identity, separation statement, Wronskian conclusion,
large-prime exclusion, or classification statement is a field of an input
record. -/
theorem classification_of_uniform_literature
    {Form Product Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (lit : SptCM.RolenLiterature.Repair.UniformRolenLiterature)
    (E : EtaJGeneratorBasis Form)
    (Analytic :
      UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid) :
    RolenClassificationStatement := by
  apply classification_of_E1_E2_and_large_exclusion lit.e1 lit.e2Finite
  intro ℓ hprime hlarge
  exact large_exclusion_of_uniform_literature lit E Analytic Grid Mult
    ℓ hprime hlarge

/-- The public endpoint, displayed without the abbreviation used by the
logical assembly module. -/
theorem canonicalCongruencePrime_iff_of_uniform_literature
    {Form Product Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (lit : SptCM.RolenLiterature.Repair.UniformRolenLiterature)
    (E : EtaJGeneratorBasis Form)
    (Analytic :
      UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid) :
    ∀ ℓ : ℕ, SptCM.CanonicalCongruencePrime ℓ ↔
      ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 :=
  classification_of_uniform_literature lit E Analytic Grid Mult

/-- Final named release theorem, relative only to the source-facing E1--E11
literature interfaces and their standard model-comparison data. -/
theorem rolen_spt_classification
    {Form Product Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (lit : SptCM.RolenLiterature.Repair.UniformRolenLiterature)
    (E : EtaJGeneratorBasis Form)
    (Analytic :
      UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization)
    (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid) :
    ∀ ℓ : ℕ, SptCM.CanonicalCongruencePrime ℓ ↔
      ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 :=
  canonicalCongruencePrime_iff_of_uniform_literature
    lit E Analytic Grid Mult

end

end SptCM.Repair
