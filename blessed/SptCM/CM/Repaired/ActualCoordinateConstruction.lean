import blessed.SptCM.CM.Repaired.I16Coordinates
import blessed.SptCM.CM.Repaired.OrientedClassActions

/-!
# Construction of the actual oriented CM coordinates

This module closes the choice gap between the oriented form classification and
`ActualOrientedCMCoordinates`.  The external analytic input is stated as the
usual transformation law for a level-six modular function, uniformly for all
oriented quadratic forms.  Descent to the quotient and all finite enumerations
are then constructed internally.
-/

namespace SptCM.CM.Repaired

noncomputable section

open SptCM.RolenLiterature
open SptCM.Arithmetic.Repaired

/-- A function on the upper half-plane obeys the level-six modular
transformation law on CM points.  This is the source-faithful E4/E7 boundary:
it is uniform in the discriminant and orientation, and says only that the
function is unchanged by a single `Γ₀(6)` change of variables. -/
def GammaZeroSixCMTransformationLaw (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ {n r : ℕ} (hn : 0 < n) (Q : RawOrientedForm n r)
    (g : GammaZeroSixMatrix)
    (hmem : transformQuadraticForm g Q.1 ∈ rawOrientedForms n r),
    F (rawCMUpperHalfPlane hn Q) =
      F (rawCMUpperHalfPlane hn
        (⟨transformQuadraticForm g Q.1, hmem⟩ : RawOrientedForm n r))

/-- The exact E4/E7 application needed here: Rolen's eta quotient has the
level-six transformation law.  This proposition is the smallest additional
literature input absent from the older predicate-only E4/E7 models. -/
abbrev E4E7AnalyticHauptmodulTransformation : Prop :=
  GammaZeroSixCMTransformationLaw analyticHauptmodul

/-- A genuine modular transformation law implies the one-step invariance used
to descend CM values to the quotient. -/
theorem rawCMValueInvariant_of_transformationLaw
    {F : UpperHalfPlane → ℂ}
    (hF : GammaZeroSixCMTransformationLaw F) {n r : ℕ} :
    RawCMValueInvariant (n := n) (r := r) F := by
  intro hn Q Q' hrel
  obtain ⟨g, hg⟩ := hrel
  have hmem : transformQuadraticForm g Q.1 ∈ rawOrientedForms n r := by
    rw [hg]
    exact Q'.2
  have h := hF hn Q g hmem
  have hsub :
      (⟨transformQuadraticForm g Q.1, hmem⟩ : RawOrientedForm n r) = Q' := by
    apply Subtype.ext
    exact hg
  simpa [hsub] using h

/-- In particular, the cited E4/E7 transformation law supplies every one of
the four invariance proofs required by `ActualOrientedCMCoordinates`. -/
theorem analyticHauptmodul_rawCMValueInvariant
    (hmodular : E4E7AnalyticHauptmodulTransformation) {n r : ℕ} :
    RawCMValueInvariant (n := n) (r := r) analyticHauptmodul :=
  rawCMValueInvariant_of_transformationLaw hmodular

/-- Turn a finite equivalence with an oriented-form quotient into the exact
finite enumeration used by the class-polynomial construction.  Choice occurs
only after finiteness and the actual cardinality have been proved. -/
def orientedCMEnumerationOfEquiv
    {n r h : ℕ} {I : Type} [Finite I]
    (e : I ≃ orientedForms n r) (hcard : Nat.card I = h) :
    OrientedCMEnumeration n r h where
  Index := I
  indexFintype := Fintype.ofFinite I
  classes := e
  card_eq := by
    rw [Fintype.card_eq_nat_card]
    exact hcard

/-- Construct all four coordinate families from the actual fixed-orientation
classification, once the class group's cardinality has been identified with
`h`.  The coordinates themselves are not chosen data: they are the genuine
analytic Hauptmodul values descended using the E4/E7 transformation law. -/
def actualOrientedCMCoordinatesOfEquivalences
    {n h : ℕ} [IsDomain (NegativeQuadraticOrder n)]
    [Finite (ClassGroup (NegativeQuadraticOrder n))]
    (hn : 0 < n)
    (E : FourOrientedClassEquivalences n)
    (hcard : Nat.card (ClassGroup (NegativeQuadraticOrder n)) = h)
    (hmodular : E4E7AnalyticHauptmodulTransformation) :
    ActualOrientedCMCoordinates n h where
  orientation1 := orientedCMEnumerationOfEquiv E.orientation1 hcard
  orientation11 := orientedCMEnumerationOfEquiv E.orientation11 hcard
  orientation5 := orientedCMEnumerationOfEquiv E.orientation5 hcard
  orientation7 := orientedCMEnumerationOfEquiv E.orientation7 hcard
  n_pos := hn
  invariant1 := analyticHauptmodul_rawCMValueInvariant hmodular
  invariant11 := analyticHauptmodul_rawCMValueInvariant hmodular
  invariant5 := analyticHauptmodul_rawCMValueInvariant hmodular
  invariant7 := analyticHauptmodul_rawCMValueInvariant hmodular

/-- Paper-facing construction.  The only external premises are the standard
quadratic-order domain theorem, the reduced-form and four-oriented-form E8
classifications, and the E4/E7 modular transformation law.  The class number,
finite index types, enumerations, and quotient invariance are deductions. -/
theorem exists_actualOrientedCMCoordinates_of_E4_E7_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hdomain : E8NegativeQuadraticOrderDomain n)
    (hforms : ∀ [IsDomain (NegativeQuadraticOrder n)],
      E8ReducedFormClassification n)
    (hOrient : ∀ [IsDomain (NegativeQuadraticOrder n)],
      E8FourOrientedFormClassification n)
    (hmodular : E4E7AnalyticHauptmodulTransformation) :
    Nonempty (ActualOrientedCMCoordinates n (negativeClassNumber n)) := by
  have hn : 0 < n := by omega
  have hfund := neg_isFundamentalDiscr hsquarefree hmod
  obtain ⟨domain⟩ := hdomain hfund
  letI : IsDomain (NegativeQuadraticOrder n) := domain
  obtain ⟨ereduced⟩ := hforms hfund
  letI : Finite (ClassGroup (NegativeQuadraticOrder n)) :=
    Finite.of_injective ereduced ereduced.injective
  obtain ⟨E⟩ := hOrient hfund hmod
  have hcard :
      Nat.card (ClassGroup (NegativeQuadraticOrder n)) =
        negativeClassNumber n := by
    exact (reduced_count_of_E8 hfund hforms).symm
  exact ⟨actualOrientedCMCoordinatesOfEquivalences hn E hcard hmodular⟩

end

end SptCM.CM.Repaired
