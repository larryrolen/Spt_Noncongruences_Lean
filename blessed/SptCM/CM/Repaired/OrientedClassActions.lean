import blessed.SptCM.Arithmetic.Repaired.ClassNumberOrientation

/-!
# The four level-six oriented ideal-class actions

The only class-field-theoretic datum used in this file is an equivalence
between the proper ideal-class group and each concrete quotient of oriented
quadratic forms.  The action itself is *not* assumed: it is transported from
left multiplication in the ideal-class group.  Its action laws, freeness,
transitivity, and the four cardinality equalities are proved below.
-/

namespace SptCM
namespace CM.Repaired

noncomputable section

open RolenLiterature
open Arithmetic.Repaired

variable {R X : Type*} [CommRing R] [IsDomain R]

/-- Transport left multiplication in the ideal-class group across a concrete
classification equivalence. -/
def transportedIdealClassAction (e : ClassGroup R ≃ X) :
    ClassGroup R → X → X :=
  fun g x => e (g * e.symm x)

@[simp] theorem transportedIdealClassAction_one
    (e : ClassGroup R ≃ X) (x : X) :
    transportedIdealClassAction e 1 x = x := by
  simp [transportedIdealClassAction]

@[simp] theorem transportedIdealClassAction_mul
    (e : ClassGroup R ≃ X) (g h : ClassGroup R) (x : X) :
    transportedIdealClassAction e (g * h) x =
      transportedIdealClassAction e g (transportedIdealClassAction e h x) := by
  simp [transportedIdealClassAction, mul_assoc]

/-- Left multiplication, transported through an equivalence, is a genuine
simply transitive ideal-class action. -/
theorem transportedIdealClassAction_isE8
    (e : ClassGroup R ≃ X) :
    E8IdealClassAction (transportedIdealClassAction e) := by
  refine ⟨⟨transportedIdealClassAction_one e,
    transportedIdealClassAction_mul e⟩, ?_⟩
  refine ⟨⟨e 1⟩, ?_⟩
  intro x y
  refine ⟨e.symm y * (e.symm x)⁻¹, ?_, ?_⟩
  · simp [transportedIdealClassAction]
  · intro g hg
    apply mul_right_cancel (b := e.symm x)
    simpa [transportedIdealClassAction] using congrArg e.symm hg

/-- The four actual actions requested in I22, together with proofs of the
standard action law and simple transitivity. -/
structure FourOrientedIdealClassActions (n : ℕ)
    [IsDomain (NegativeQuadraticOrder n)] where
  action1 : ClassGroup (NegativeQuadraticOrder n) →
    orientedForms n 1 → orientedForms n 1
  action11 : ClassGroup (NegativeQuadraticOrder n) →
    orientedForms n 11 → orientedForms n 11
  action5 : ClassGroup (NegativeQuadraticOrder n) →
    orientedForms n 5 → orientedForms n 5
  action7 : ClassGroup (NegativeQuadraticOrder n) →
    orientedForms n 7 → orientedForms n 7
  action1_isE8 : E8IdealClassAction action1
  action11_isE8 : E8IdealClassAction action11
  action5_isE8 : E8IdealClassAction action5
  action7_isE8 : E8IdealClassAction action7

/-- A domain witness together with the four constructed actions.  Packaging
the instance removes any hidden typeclass premise from the public I22
construction. -/
structure FourOrientedIdealClassActionsWitness (n : ℕ) where
  domain : IsDomain (NegativeQuadraticOrder n)
  actions : @FourOrientedIdealClassActions n domain

/-- I22 action construction: transport the regular ideal-class action across
all four fixed-orientation form/ideal correspondences. -/
def fourOrientedIdealClassActions
    {n : ℕ} [IsDomain (NegativeQuadraticOrder n)]
    (E : FourOrientedClassEquivalences n) :
    FourOrientedIdealClassActions n where
  action1 := transportedIdealClassAction E.orientation1
  action11 := transportedIdealClassAction E.orientation11
  action5 := transportedIdealClassAction E.orientation5
  action7 := transportedIdealClassAction E.orientation7
  action1_isE8 := transportedIdealClassAction_isE8 E.orientation1
  action11_isE8 := transportedIdealClassAction_isE8 E.orientation11
  action5_isE8 := transportedIdealClassAction_isE8 E.orientation5
  action7_isE8 := transportedIdealClassAction_isE8 E.orientation7

/-- I22: the exact E8 fixed-orientation classification induces the four
actual simply transitive actions; the actions are constructed here rather
than stored in the external interface. -/
theorem fourOrientedIdealClassActions_withDomain_of_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    [IsDomain (NegativeQuadraticOrder n)]
    (hOrient : E8FourOrientedFormClassification n) :
    Nonempty (FourOrientedIdealClassActions n) := by
  obtain ⟨E⟩ := hOrient (neg_isFundamentalDiscr hsquarefree hmod) hmod
  exact ⟨fourOrientedIdealClassActions E⟩

/-- I22 without a hidden domain typeclass: the standard domain theorem is
used to install the concrete quadratic-order instance before constructing the
four actions. -/
theorem fourOrientedIdealClassActions_of_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hdomain : E8NegativeQuadraticOrderDomain n)
    (hOrient : ∀ [IsDomain (NegativeQuadraticOrder n)],
      E8FourOrientedFormClassification n) :
    Nonempty (FourOrientedIdealClassActionsWitness n) := by
  have hfund := neg_isFundamentalDiscr hsquarefree hmod
  obtain ⟨domain⟩ := hdomain hfund
  letI : IsDomain (NegativeQuadraticOrder n) := domain
  obtain ⟨A⟩ := fourOrientedIdealClassActions_withDomain_of_E8
    hsquarefree hmod hOrient
  exact ⟨⟨domain, A⟩⟩

/-- I22 actual count theorem.  The class actions and all four count equalities
are conclusions.  The hypotheses are exactly the two standard E8
classifications: ordinary reduced forms and the four fixed local
orientations. -/
theorem actualClassCountSpec_withDomain_of_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    [IsDomain (NegativeQuadraticOrder n)]
    (hforms : E8ReducedFormClassification n)
    (hOrient : E8FourOrientedFormClassification n) :
    ClassCountSpec n := by
  have hfund := neg_isFundamentalDiscr hsquarefree hmod
  obtain ⟨ereduced⟩ := hforms hfund
  letI : Finite (ClassGroup (NegativeQuadraticOrder n)) :=
    Finite.of_injective ereduced ereduced.injective
  obtain ⟨A⟩ := fourOrientedIdealClassActions_withDomain_of_E8
    hsquarefree hmod hOrient
  exact classCountSpec_of_E8 hsquarefree hmod hforms
    A.action1 A.action11 A.action5 A.action7
    A.action1_isE8 A.action11_isE8 A.action5_isE8 A.action7_isE8

/-- The fully discharged I22 count theorem.  Its only premises are the exact
standard domain, ordinary reduced-form, and fixed-orientation
form/ideal-class statements. -/
theorem actualClassCountSpec_of_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hdomain : E8NegativeQuadraticOrderDomain n)
    (hforms : ∀ [IsDomain (NegativeQuadraticOrder n)],
      E8ReducedFormClassification n)
    (hOrient : ∀ [IsDomain (NegativeQuadraticOrder n)],
      E8FourOrientedFormClassification n) :
    ClassCountSpec n := by
  have hfund := neg_isFundamentalDiscr hsquarefree hmod
  obtain ⟨domain⟩ := hdomain hfund
  letI : IsDomain (NegativeQuadraticOrder n) := domain
  exact actualClassCountSpec_withDomain_of_E8
    hsquarefree hmod hforms hOrient

end

end CM.Repaired
end SptCM
