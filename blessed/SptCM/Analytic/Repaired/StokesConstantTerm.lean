module

public import blessed.SptCM.Analytic.Repaired.AuxiliaryForms
public import blessed.SptCM.Analytic.PaperCoefficientModels
public import blessed.SptCM.Analytic.DualityPairing
public import blessed.SptCM.Literature.RolenLiterature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# The internal constant-term cancellation in the Stokes pairing

The analytic Stokes identity is external.  This file proves the
paper-specific coefficient cancellation to which it is applied.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic
open SptCM.RolenLiterature
open scoped BigOperators

/-- The genuinely coefficient-theoretic constant term of `H f`, written as a
finite convolution once `H` has no terms below `-n` and `f` has no negative
terms below `-1`. -/
@[expose]
noncomputable def finiteMockProductConstantTerm (n : ℕ) (H : HForm ℤ) : ℤ :=
  ∑ r ∈ Finset.Icc (-(n : ℤ)) 1, H r * aCoeff (-r)

/-- The two possible contributions to `[q⁰](H_n f)`: the polar coefficient
of `H_n` paired with `a(n)`, and its index-one coefficient paired with the
unique negative coefficient `a(-1)` of `f`. -/
@[expose]
def hnMockProductConstantTerm (n : ℕ) (H : HForm ℤ) : ℤ :=
  H (-(n : ℤ)) * aCoeff n + H 1 * aCoeff (-1)

/-- Under the exact auxiliary normalization, every term of the finite
constant-term convolution except the two displayed endpoint terms vanishes. -/
theorem finiteMockProductConstantTerm_eq_hnMockProductConstantTerm
    (n : ℕ) (hn : 0 < n) (H : HForm ℤ)
    (hH : HasHnNormalization n (aCoeff n) H) :
    finiteMockProductConstantTerm n H = hnMockProductConstantTerm n H := by
  let s : Finset ℤ := Finset.Icc (-(n : ℤ)) 1
  let f : ℤ → ℤ := fun r => H r * aCoeff (-r)
  have hneg : (-(n : ℤ)) ∈ s := by simp [s]
  have hone : (1 : ℤ) ∈ s.erase (-(n : ℤ)) := by
    simp [s]
    omega
  have hrest : ∑ r ∈ (s.erase (-(n : ℤ))).erase 1, f r = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp only [Finset.mem_erase] at hr
    have hr1 : r ≠ 1 := hr.1
    have hrneg : r ≠ -(n : ℤ) := hr.2.1
    have hrs : r ∈ s := hr.2.2
    have hrle : r ≤ 1 := (Finset.mem_Icc.mp hrs).2
    have hHr : H r = 0 := hH.2.2 r (by omega) hrneg hr1
    simp [f, hHr]
  have hsum1 := Finset.sum_erase_add (s.erase (-(n : ℤ))) f hone
  have hsumneg := Finset.sum_erase_add s f hneg
  rw [hrest, zero_add] at hsum1
  have hcalc : (∑ r ∈ s, f r) = f (-(n : ℤ)) + f 1 := by
    calc
      (∑ r ∈ s, f r) = (∑ r ∈ s.erase (-(n : ℤ)), f r) +
          f (-(n : ℤ)) := hsumneg.symm
      _ = f 1 + f (-(n : ℤ)) := by rw [← hsum1]
      _ = f (-(n : ℤ)) + f 1 := add_comm _ _
  simpa [finiteMockProductConstantTerm, hnMockProductConstantTerm, s, f]
    using hcalc

/-- For the actually normalized auxiliary series, the two surviving
constant-term contributions are `a(n)` and `-a(n)`, hence cancel. -/
theorem hnMockProductConstantTerm_eq_zero
    (n : ℕ) (H : HForm ℤ)
    (hH : HasHnNormalization n (aCoeff n) H) :
    hnMockProductConstantTerm n H = 0 := by
  rw [hnMockProductConstantTerm, hH.1, hH.2.1, aCoeff_neg_one]
  ring

/-- The cancellation specialized to the triangularly constructed actual
auxiliary form. -/
theorem auxiliaryHn_mockProductConstantTerm_eq_zero
    {Form : Type*} (E : SptCM.Analytic.Repaired.EtaJPowerBasis Form)
    (k : ℕ) (hk : 0 < k) :
    hnMockProductConstantTerm (24 * k - 1)
      (SptCM.Analytic.Repaired.auxiliaryHn E k
        (aCoeff ((24 * k - 1 : ℕ) : ℤ))) = 0 := by
  exact hnMockProductConstantTerm_eq_zero _ _
    (SptCM.Analytic.Repaired.auxiliaryHn_normalization E k hk
      (aCoeff ((24 * k - 1 : ℕ) : ℤ)))

/-! ## The actual finite-height application -/

/-- The numerical shadow factor in the paper's Stokes formula. -/
@[expose]
noncomputable def publishedShadowScale : ℝ :=
  3 * Real.sqrt 6 / Real.pi

/-- Bringmann's published shadow factor is nonzero. -/
theorem publishedShadowScale_ne_zero : publishedShadowScale ≠ 0 := by
  unfold publishedShadowScale
  positivity

/-- A Stokes input remembers the coefficient series to which the completion
is paired.  It contains no boundary identity, limit, or pairing conclusion. -/
structure HnStokesInput (Completion : Type*) where
  index : ℕ
  coefficients : HForm ℤ
  completion : Completion

/-- The concrete finite-height Stokes model used in the paper.  Its scale and
holomorphic boundary term are fixed definitions: only the genuinely analytic
qualification, truncated integrals, errors, and regularized values are
parameters. -/
@[expose]
noncomputable def hnFiniteHeightStokesModel
    {Completion : Type*}
    (qualified : HnStokesInput Completion → Prop)
    (truncatedIntegral topBoundaryError :
      HnStokesInput Completion → ℕ → ℝ)
    (regularizedValue : HnStokesInput Completion → ℝ) :
    FiniteHeightStokesModel (HnStokesInput Completion) where
  qualified := qualified
  shadowScale := fun _ => publishedShadowScale
  truncatedIntegral := truncatedIntegral
  holomorphicConstantTerm := fun x =>
    (finiteMockProductConstantTerm x.index x.coefficients : ℝ)
  topBoundaryError := topBoundaryError
  regularizedPairing := regularizedValue

/-- The actual pair consisting of the triangularly constructed `H_n` and a
chosen Bringmann completion. -/
@[expose]
noncomputable def actualHnStokesInput
    {Form Completion : Type*} (E : EtaJPowerBasis Form)
    (k : ℕ) (F : Completion) : HnStokesInput Completion where
  index := 24 * k - 1
  coefficients :=
    auxiliaryHn E k (aCoeff ((24 * k - 1 : ℕ) : ℤ))
  completion := F

/-- Exact output required from the paper-specific Stokes application.  The
two surviving holomorphic contributions are displayed as `a(n) - a(n)`;
the finite-height identity and the two limits come from the general theorem. -/
structure ActualHnFiniteHeightStokesSpec
    {Completion : Type*}
    (M : FiniteHeightStokesModel (HnStokesInput Completion))
    (x : HnStokesInput Completion) (n : ℕ) : Prop where
  shadowScale_eq : M.shadowScale x = publishedShadowScale
  shadowScale_ne_zero : M.shadowScale x ≠ 0
  constantTerm_eq :
    M.holomorphicConstantTerm x =
      (aCoeff n : ℝ) - (aCoeff n : ℝ)
  finiteHeightIdentity : ∀ T,
    M.shadowScale x * M.truncatedIntegral x T =
      M.holomorphicConstantTerm x + M.topBoundaryError x T
  truncatedIntegral_tendsto :
    Filter.Tendsto (M.truncatedIntegral x) Filter.atTop
      (nhds (M.regularizedPairing x))
  topBoundaryError_tendsto :
    Filter.Tendsto (M.topBoundaryError x) Filter.atTop (nhds 0)

/-- I09, finite-height application.  Bringmann supplies an actual completion;
qualification of that pair lets the general finite-height theorem produce the
boundary identity and both limits.  The internally proved Fourier
normalization reduces its holomorphic boundary term to `a(n) - a(n)`. -/
theorem auxiliaryHn_finiteHeightStokesApplication
    {Form Completion Series : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (hk : 0 < k)
    (HM : HarmonicMaassModel Completion Series)
    (f eta : Series) (shadowNormalization : Series → Series)
    (hBringmann : BringmannCompletion HM f eta shadowNormalization)
    (qualified : HnStokesInput Completion → Prop)
    (truncatedIntegral topBoundaryError :
      HnStokesInput Completion → ℕ → ℝ)
    (regularizedValue : HnStokesInput Completion → ℝ)
    (hqualified : ∀ F,
      HM.holomorphicPart F = f →
      HM.shadow F = shadowNormalization eta →
      qualified (actualHnStokesInput E k F))
    (hStokes : FiniteHeightStokesTheorem
      (hnFiniteHeightStokesModel qualified truncatedIntegral
        topBoundaryError regularizedValue)) :
    ∃ F : Completion,
      HM.holomorphicPart F = f ∧
      HM.shadow F = shadowNormalization eta ∧
      ActualHnFiniteHeightStokesSpec
        (hnFiniteHeightStokesModel qualified truncatedIntegral
          topBoundaryError regularizedValue)
        (actualHnStokesInput E k F) (24 * k - 1) := by
  rcases hBringmann with ⟨F, hhol, hshadow⟩
  let M := hnFiniteHeightStokesModel qualified truncatedIntegral
    topBoundaryError regularizedValue
  let x := actualHnStokesInput E k F
  have hconclusion : FiniteHeightStokesConclusion M x :=
    hStokes x (hqualified F hhol hshadow)
  rcases hconclusion with ⟨hidentity, hbulk, herror⟩
  refine ⟨F, hhol, hshadow, ?_⟩
  refine
    { shadowScale_eq := rfl
      shadowScale_ne_zero := publishedShadowScale_ne_zero
      constantTerm_eq := ?_
      finiteHeightIdentity := hidentity
      truncatedIntegral_tendsto := hbulk
      topBoundaryError_tendsto := herror }
  change
    (finiteMockProductConstantTerm (24 * k - 1)
      (auxiliaryHn E k (aCoeff ((24 * k - 1 : ℕ) : ℤ))) : ℝ) =
      (aCoeff ((24 * k - 1 : ℕ) : ℤ) : ℝ) -
        (aCoeff ((24 * k - 1 : ℕ) : ℤ) : ℝ)
  rw [finiteMockProductConstantTerm_eq_hnMockProductConstantTerm
    (24 * k - 1) (by omega)
    (auxiliaryHn E k (aCoeff ((24 * k - 1 : ℕ) : ℤ)))
    (auxiliaryHn_normalization E k hk
      (aCoeff ((24 * k - 1 : ℕ) : ℤ)))]
  have hzero := auxiliaryHn_mockProductConstantTerm_eq_zero E k hk
  norm_num [hzero]

/-- I09, specialized pairing.  The exact finite-height application gives the
Stokes pairing data, its internally computed constant term is zero, and the
published shadow scale is nonzero. -/
theorem auxiliaryHn_regularizedPairing_eq_zero
    {Completion : Type*}
    (M : FiniteHeightStokesModel (HnStokesInput Completion))
    (x : HnStokesInput Completion) (n : ℕ)
    (h : ActualHnFiniteHeightStokesSpec M x n) :
    M.regularizedPairing x = 0 := by
  let d : StokesPairingData :=
    { scale := M.shadowScale x
      pairing := M.regularizedPairing x
      constantTerm := M.holomorphicConstantTerm x
      bulk := M.truncatedIntegral x
      error := M.topBoundaryError x
      bulk_tendsto := h.truncatedIntegral_tendsto
      error_tendsto := h.topBoundaryError_tendsto
      finite_height_identity := h.finiteHeightIdentity }
  have hconstant : d.constantTerm = 0 := by
    change M.holomorphicConstantTerm x = 0
    rw [h.constantTerm_eq]
    ring
  exact d.pairing_eq_zero h.shadowScale_ne_zero hconstant

/-- I09 in its end-to-end form: for every positive `k`, Bringmann's
completion and the general finite-height Stokes theorem give a completion for
which the correctly normalized regularized pairing with the actual
`H_(24k-1)` vanishes. -/
theorem auxiliaryHn_stokesPairing_eq_zero
    {Form Completion Series : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (hk : 0 < k)
    (HM : HarmonicMaassModel Completion Series)
    (f eta : Series) (shadowNormalization : Series → Series)
    (hBringmann : BringmannCompletion HM f eta shadowNormalization)
    (qualified : HnStokesInput Completion → Prop)
    (truncatedIntegral topBoundaryError :
      HnStokesInput Completion → ℕ → ℝ)
    (regularizedValue : HnStokesInput Completion → ℝ)
    (hqualified : ∀ F,
      HM.holomorphicPart F = f →
      HM.shadow F = shadowNormalization eta →
      qualified (actualHnStokesInput E k F))
    (hStokes : FiniteHeightStokesTheorem
      (hnFiniteHeightStokesModel qualified truncatedIntegral
        topBoundaryError regularizedValue)) :
    ∃ F : Completion,
      HM.holomorphicPart F = f ∧
      HM.shadow F = shadowNormalization eta ∧
      regularizedValue (actualHnStokesInput E k F) = 0 := by
  obtain ⟨F, hhol, hshadow, hspec⟩ :=
    auxiliaryHn_finiteHeightStokesApplication E k hk HM f eta
      shadowNormalization hBringmann qualified truncatedIntegral
      topBoundaryError regularizedValue hqualified hStokes
  refine ⟨F, hhol, hshadow, ?_⟩
  exact auxiliaryHn_regularizedPairing_eq_zero
    (hnFiniteHeightStokesModel qualified truncatedIntegral
      topBoundaryError regularizedValue)
    (actualHnStokesInput E k F) (24 * k - 1) hspec

end SptCM.Analytic.Repaired
