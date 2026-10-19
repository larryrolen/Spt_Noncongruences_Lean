import blessed.SptCM.Analytic.Repaired.CuspContractions
import blessed.SptCM.Literature.RolenLiterature
import blessed.SptCM.Analytic.Repaired.StokesConstantTerm

/-!
# The four concrete Weyl-vector calculations

This module specializes the general Bruinier--Schwagenscheidt formula to the
component theta functions used in the SPT argument.  The only analytic input
about those theta functions is Euler's exact signed component identity; all
four Atkin--Lehner signs and the resulting contractions are computed in the
project.
-/

namespace SptCM.Analytic.Repaired

open SptCM.RolenLiterature

/-- The Weyl-vector model in which the regularized pairing is the signed sum
of the twelve component pairings and the cusp theta function is obtained by
the explicit Atkin--Lehner permutation. -/
def componentWeylVectorModel
    {Input V : Type*} [AddCommMonoid V] [Module ℂ V]
    (admissible : Input → Prop) (weylVector : Input → ℕ → ℂ)
    (pairing : Input → V →ₗ[ℂ] ℂ) (theta : Fin 12 → V)
    (normalization : ℂ → ℂ) :
    WeylVectorModel Input (Fin 12 → V) ℂ ℕ where
  admissibleInput := admissible
  weylVector := weylVector
  regularizedPairing := fun F componentTheta =>
    ∑ r, (chiTwelveResidue r : ℂ) * pairing F (componentTheta r)
  cuspTheta := fun c r => theta (atkinLehnerSigma c r)
  normalization := normalization

@[simp] theorem componentWeylVectorModel_pairing
    {Input V : Type*} [AddCommMonoid V] [Module ℂ V]
    (admissible : Input → Prop) (weylVector : Input → ℕ → ℂ)
    (pairing : Input → V →ₗ[ℂ] ℂ) (theta : Fin 12 → V)
    (normalization : ℂ → ℂ) (F : Input) (c : ℕ) :
    (componentWeylVectorModel admissible weylVector pairing theta normalization).regularizedPairing F
          ((componentWeylVectorModel admissible weylVector pairing theta
            normalization).cuspTheta c) =
      regularizedCuspThetaContraction (pairing F) c theta := by
  rfl

/-- I11: for the concrete component model, the general E6 formula and the
internally verified four contraction calculations force all four level-six
Weyl vectors to vanish.  No Weyl-vector vanishing statement occurs among the
hypotheses. -/
theorem componentWeylVectors_eq_zero
    {Input V : Type*} [AddCommMonoid V] [Module ℂ V]
    (admissible : Input → Prop) (weylVector : Input → ℕ → ℂ)
    (pairing : Input → V →ₗ[ℂ] ℂ) (theta : Fin 12 → V) (eta : V)
    (normalization : ℂ → ℂ)
    (hE6 : E6BruinierSchwagenscheidt
      (componentWeylVectorModel admissible weylVector pairing theta
        normalization))
    (heta : EtaComponentThetaIdentity theta eta)
    (F : Input) (hadmissible : admissible F)
    (hpairing : pairing F eta = 0)
    (hnormalization : normalization 0 = 0) :
    ∀ c, IsLevelSixDivisor c → weylVector F c = 0 := by
  intro c hc
  change (componentWeylVectorModel admissible weylVector pairing theta
    normalization).weylVector F c = 0
  rw [hE6 F c hadmissible]
  rw [componentWeylVectorModel_pairing]
  rw [regularizedCuspThetaContraction_eq_signed_eta
    (pairing F) theta eta heta c hc, hpairing]
  simp only [mul_zero]
  change normalization 0 = 0
  exact hnormalization


/-- I11 specialized to the actual triangular auxiliary form.  The scalar
pairing is the one already evaluated by the finite-height Stokes argument;
`hcompat` merely identifies its complex-linear realization with that same
regularized integral. -/
theorem auxiliaryHn_componentWeylVectors_eq_zero
    {Form Completion V : Type*} [AddCommMonoid V] [Module ℂ V]
    (E : EtaJPowerBasis Form) (k : ℕ) (F : Completion)
    (M : FiniteHeightStokesModel (HnStokesInput Completion))
    (hspec : ActualHnFiniteHeightStokesSpec M
      (actualHnStokesInput E k F) (24 * k - 1))
    (admissible : HnStokesInput Completion → Prop)
    (weylVector : HnStokesInput Completion → ℕ → ℂ)
    (pairing : HnStokesInput Completion → V →ₗ[ℂ] ℂ)
    (theta : Fin 12 → V) (eta : V) (normalization : ℂ → ℂ)
    (hE6 : E6BruinierSchwagenscheidt
      (componentWeylVectorModel admissible weylVector pairing theta
        normalization))
    (heta : EtaComponentThetaIdentity theta eta)
    (hadmissible : admissible (actualHnStokesInput E k F))
    (hcompat : pairing (actualHnStokesInput E k F) eta =
      (M.regularizedPairing (actualHnStokesInput E k F) : ℂ))
    (hnormalization : normalization 0 = 0) :
    ∀ c, IsLevelSixDivisor c →
      weylVector (actualHnStokesInput E k F) c = 0 := by
  apply componentWeylVectors_eq_zero admissible weylVector pairing theta eta
    normalization hE6 heta (actualHnStokesInput E k F) hadmissible
  · rw [hcompat, auxiliaryHn_regularizedPairing_eq_zero M
      (actualHnStokesInput E k F) (24 * k - 1) hspec]
    simp
  · exact hnormalization


/-! ## Real realization used by the finite-height Stokes integral -/

/-- Euler's signed component identity in the real series space used by the
finite-height integral. -/
def RealEtaComponentThetaIdentity
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (theta : Fin 12 → V) (eta : V) : Prop :=
  (∑ r, (chiTwelveResidue r : ℝ) • theta r) = (2 : ℝ) • eta

/-- The real component pairing at the cusp indexed by `c`. -/
def realRegularizedCuspThetaContraction
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (pairing : V →ₗ[ℝ] ℝ) (c : ℕ) (theta : Fin 12 → V) : ℝ :=
  ∑ r, (chiTwelveResidue r : ℝ) *
    pairing (theta (atkinLehnerSigma c r))

/-- The same `+,-,-,+` contraction formula over the real scalar field in
which the Stokes integral takes its values. -/
theorem realRegularizedCuspThetaContraction_eq_signed_eta
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (pairing : V →ₗ[ℝ] ℝ) (theta : Fin 12 → V) (eta : V)
    (heta : RealEtaComponentThetaIdentity theta eta)
    (c : ℕ) (hc : IsLevelSixDivisor c) :
    realRegularizedCuspThetaContraction pairing c theta =
      (atkinLehnerEigenvalue c : ℝ) * (2 * pairing eta) := by
  have hunpermuted :
      (∑ r, (chiTwelveResidue r : ℝ) * pairing (theta r)) =
        2 * pairing eta := by
    have hmap := congrArg pairing heta
    simpa [RealEtaComponentThetaIdentity, map_sum, map_smul] using hmap
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [realRegularizedCuspThetaContraction, atkinLehnerSigma,
      atkinLehnerMultiplier, atkinLehnerEigenvalue, chiTwelveResidue,
      Fin.sum_univ_succ] at hunpermuted ⊢ <;> linarith

/-- The real Weyl model whose pairing is definitionally the twelve-component
regularized pairing and whose cusp theta functions use the computed
Atkin--Lehner permutations. -/
def realComponentWeylVectorModel
    {Input V : Type*} [AddCommMonoid V] [Module ℝ V]
    (admissible : Input → Prop) (weylVector : Input → ℕ → ℝ)
    (pairing : Input → V →ₗ[ℝ] ℝ) (theta : Fin 12 → V)
    (normalization : ℝ → ℝ) :
    WeylVectorModel Input (Fin 12 → V) ℝ ℕ where
  admissibleInput := admissible
  weylVector := weylVector
  regularizedPairing := fun F componentTheta =>
    ∑ r, (chiTwelveResidue r : ℝ) * pairing F (componentTheta r)
  cuspTheta := fun c r => theta (atkinLehnerSigma c r)
  normalization := normalization

/-- I11 in the exact real-valued model shared with the Stokes calculation.
The scalar regularized value is definitionally `pairing F eta`; hence no
paper-specific pairing comparison is assumed. -/
theorem auxiliaryHn_realComponentWeylVectors_eq_zero
    {Form Completion V : Type*} [AddCommMonoid V] [Module ℝ V]
    (E : EtaJPowerBasis Form) (k : ℕ) (F : Completion)
    (qualified : HnStokesInput Completion → Prop)
    (truncatedIntegral topBoundaryError :
      HnStokesInput Completion → ℕ → ℝ)
    (admissible : HnStokesInput Completion → Prop)
    (weylVector : HnStokesInput Completion → ℕ → ℝ)
    (pairing : HnStokesInput Completion → V →ₗ[ℝ] ℝ)
    (theta : Fin 12 → V) (eta : V) (normalization : ℝ → ℝ)
    (hspec : ActualHnFiniteHeightStokesSpec
      (hnFiniteHeightStokesModel qualified truncatedIntegral topBoundaryError
        (fun x => pairing x eta))
      (actualHnStokesInput E k F) (24 * k - 1))
    (hE6 : E6BruinierSchwagenscheidt
      (realComponentWeylVectorModel admissible weylVector pairing theta
        normalization))
    (heta : RealEtaComponentThetaIdentity theta eta)
    (hadmissible : admissible (actualHnStokesInput E k F))
    (hnormalization : normalization 0 = 0) :
    ∀ c, IsLevelSixDivisor c →
      weylVector (actualHnStokesInput E k F) c = 0 := by
  intro c hc
  let x := actualHnStokesInput E k F
  let M := hnFiniteHeightStokesModel qualified truncatedIntegral
    topBoundaryError (fun y => pairing y eta)
  have hscalar : pairing x eta = 0 := by
    exact auxiliaryHn_regularizedPairing_eq_zero M x (24 * k - 1) hspec
  change (realComponentWeylVectorModel admissible weylVector pairing theta
    normalization).weylVector x c = 0
  rw [hE6 x c hadmissible]
  change normalization
    (realRegularizedCuspThetaContraction (pairing x) c theta) = 0
  rw [realRegularizedCuspThetaContraction_eq_signed_eta
    (pairing x) theta eta heta c hc, hscalar]
  simp [hnormalization]

end SptCM.Analytic.Repaired
