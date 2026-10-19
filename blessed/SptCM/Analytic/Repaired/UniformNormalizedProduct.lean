import blessed.SptCM.Analytic.Repaired.I12NormalizedProduct
set_option maxHeartbeats 4000000

/-!
# Uniform source-facing construction of the normalized I12 identity

This module packages the analytic models used in E3--E6 without storing the
normalized Borcherds-product identity.  The only paper-specific comparison
field identifies the regularized pairing of the concrete four-component input
with the finite-height Stokes pairing of the same auxiliary form.  The
normalized quotient is then derived from the checked Stokes, Weyl-vector,
divisor, cusp, and leading-term chain.
-/

namespace SptCM.Analytic.Repaired

open SptCM.RolenLiterature

noncomputable section

set_option maxHeartbeats 2000000

/-- Uniform analytic source data for the actual auxiliary forms.  All fields
are either general external theorems (E3, E5, E6 and the finite-height Stokes
principle) or application comparisons between the concrete models.  In
particular, this structure has no field asserting a product identity,
Wronskian statement, polynomial separation, or prime classification. -/
structure UniformActualNormalizedProductPackage
    (Form Completion Series V : Type*) [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    (E : EtaJGeneratorBasis Form) where
  harmonicMaass : HarmonicMaassModel Completion Series
  mockSeries : Series
  etaSeries : Series
  shadowNormalization : Series → Series
  bringmann : BringmannCompletion harmonicMaass mockSeries etaSeries
    shadowNormalization
  stokesQualified : HnStokesInput Completion → Prop
  truncatedIntegral : HnStokesInput Completion → ℕ → ℝ
  topBoundaryError : HnStokesInput Completion → ℕ → ℝ
  regularizedValue : HnStokesInput Completion → ℝ
  qualification : ∀ (k : ℕ) (F : Completion),
    harmonicMaass.holomorphicPart F = mockSeries →
    harmonicMaass.shadow F = shadowNormalization etaSeries →
    stokesQualified (actualHnStokesInput E.toEtaJPowerBasis k F)
  finiteHeightStokes : FiniteHeightStokesTheorem
    (hnFiniteHeightStokesModel stokesQualified truncatedIntegral
      topBoundaryError regularizedValue)
  lift : FourComponentInput Form → LaurentSeries ℚ
  unitary : LaurentSeries ℚ → Prop
  geometry : I12MeromorphicGeometry
    (LaurentSeries ℚ) I12Divisor I12Divisor ℚ
  bruinierOno : ∀ n : ℕ, E5BruinierOno
    (actualI12BorcherdsModel E n lift geometry.divisor unitary)
  weylVector : FourComponentInput Form → ℕ → ℂ
  pairing : FourComponentInput Form → V →ₗ[ℂ] ℂ
  componentTheta : Fin 12 → V
  etaTheta : V
  normalization : ℂ → ℂ
  bruinierSchwagenscheidt : ∀ n : ℕ,
    E6BruinierSchwagenscheidt
      (componentWeylVectorModel (VectorInputSpec E n) weylVector pairing
        componentTheta normalization)
  etaComponentIdentity : EtaComponentThetaIdentity componentTheta etaTheta
  normalization_zero : normalization 0 = 0
  pairingComparison : ∀ (k : ℕ) (F : Completion),
    harmonicMaass.holomorphicPart F = mockSeries →
    harmonicMaass.shadow F = shadowNormalization etaSeries →
    pairing
        (auxiliaryFourComponentInput E k
          (aCoeff ((24 * k - 1 : ℕ) : ℤ))) etaTheta =
      (regularizedValue
        (actualHnStokesInput E.toEtaJPowerBasis k F) : ℂ)
  divisorRigidity : I12DivisorRigidityPrinciple geometry
  leadingValue : I12LeadingValuePrinciple geometry
  leadingCoefficient : ∀ f : LaurentSeries ℚ,
    geometry.leadingValue f = f.coeff 0
  classPolynomialDivisor : I12ClassPolynomialDivisorPrinciple geometry
  classPolynomialCusp : I12ClassPolynomialCuspPrinciple geometry
  weylCusp : I12WeylCuspPrinciple geometry lift weylVector

/-- If `n` is written as its triangular index `24k-1`, E3 and the
finite-height Stokes theorem first force the actual scalar pairing to vanish.
E6 then kills all cusp Weyl vectors, and E5 plus the general curve laws derives
the normalized actual class-polynomial/Euler-product identity.  Keeping `n`
as an independent parameter avoids any transport of the dependent CM
coordinate structure. -/
theorem UniformActualNormalizedProductPackage.normalizedIdentityOfIndexEq
    {Form Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    {E : EtaJGeneratorBasis Form}
    (P : UniformActualNormalizedProductPackage Form Completion Series V E)
    {n h : ℕ} (k : ℕ) (hk : 0 < k) (hn : n = 24 * k - 1)
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent =
      actualBorcherdsEulerQuotient
        (auxiliaryFourComponentInput E k (aCoeff (n : ℤ))) := by
  obtain ⟨F, hhol, hshadow, hpairingReal⟩ :=
    auxiliaryHn_stokesPairing_eq_zero E.toEtaJPowerBasis k hk
      P.harmonicMaass P.mockSeries P.etaSeries P.shadowNormalization
      P.bringmann P.stokesQualified P.truncatedIntegral P.topBoundaryError
      P.regularizedValue (P.qualification k) P.finiteHeightStokes
  have hAtri : VectorInputSpec E (24 * k - 1)
      (auxiliaryFourComponentInput E k (aCoeff (n : ℤ))) :=
    auxiliaryHn_vectorInputSpec E k hk (aCoeff (n : ℤ))
  have hA : VectorInputSpec E n
      (auxiliaryFourComponentInput E k (aCoeff (n : ℤ))) :=
    hn.symm ▸ hAtri
  have hcomparison : P.pairing
      (auxiliaryFourComponentInput E k (aCoeff (n : ℤ))) P.etaTheta =
      (P.regularizedValue
        (actualHnStokesInput E.toEtaJPowerBasis k F) : ℂ) := by
    have hcoeff :
        aCoeff (n : ℤ) = aCoeff ((24 * k - 1 : ℕ) : ℤ) := by
      rw [hn]
    simpa only [hcoeff] using P.pairingComparison k F hhol hshadow
  have hpairing : P.pairing
      (auxiliaryFourComponentInput E k (aCoeff (n : ℤ))) P.etaTheta = 0 := by
    rw [hcomparison, hpairingReal]
    norm_num
  exact actualClassPolynomialLaurentQuotient_eq_canonicalEulerQuotient
    E D P.lift P.unitary P.geometry (P.bruinierOno n)
    (auxiliaryFourComponentInput E k (aCoeff (n : ℤ)))
    (by omega) hA P.weylVector P.pairing P.componentTheta P.etaTheta
    P.normalization (P.bruinierSchwagenscheidt n)
    P.etaComponentIdentity hpairing P.normalization_zero P.divisorRigidity
    P.leadingValue P.leadingCoefficient P.classPolynomialDivisor
    P.classPolynomialCusp P.weylCusp

/-- The preceding theorem at a literal triangular index. -/
theorem UniformActualNormalizedProductPackage.normalizedIdentityAtIndex
    {Form Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    {E : EtaJGeneratorBasis Form}
    (P : UniformActualNormalizedProductPackage Form Completion Series V E)
    (k : ℕ) (hk : 0 < k) {h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates (24 * k - 1) h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent =
      actualBorcherdsEulerQuotient
        (auxiliaryFourComponentInput E k
          (aCoeff (((24 * k - 1 : ℕ)) : ℤ))) := by
  exact P.normalizedIdentityOfIndexEq k hk rfl D

/-- The arithmetic progression condition used in the paper identifies every
eligible discriminant with its triangular index. -/
lemma index_eq_twentyFour_mul_div_of_mod_eq_twentyThree
    {n : ℕ} (hmod : n % 24 = 23) :
    n = 24 * ((n + 1) / 24) - 1 := by
  have hn1mod : (n + 1) % 24 = 0 := by omega
  have hn1 : n + 1 = 24 * ((n + 1) / 24) := by
    conv_lhs => rw [← Nat.mod_add_div (n + 1) 24]
    rw [hn1mod, zero_add]
  omega

/-- Uniform form of the normalized I12 identity for every eligible
`n ≡ 23 (mod 24)`.  The class-polynomial specification is an input produced
by the independent E8 descent chain; the analytic quotient equality itself
is proved here and is not stored in the package. -/
theorem UniformActualNormalizedProductPackage.normalizedIdentity
    {Form Completion Series V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V]
    {E : EtaJGeneratorBasis Form}
    (P : UniformActualNormalizedProductPackage Form Completion Series V E)
    {n h : ℕ} (hmod : n % 24 = 23)
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent =
      actualBorcherdsEulerQuotient
        (auxiliaryFourComponentInput E ((n + 1) / 24)
          (aCoeff (n : ℤ))) := by
  let k := (n + 1) / 24
  have hn : n = 24 * k - 1 := by
    simpa [k] using
      index_eq_twentyFour_mul_div_of_mod_eq_twentyThree hmod
  have hk : 0 < k := by
    have hn23 : 23 ≤ n := by
      rw [← hmod]
      exact Nat.mod_le n 24
    simp only [k]
    omega
  exact P.normalizedIdentityOfIndexEq k hk hn D

end

end SptCM.Analytic.Repaired
