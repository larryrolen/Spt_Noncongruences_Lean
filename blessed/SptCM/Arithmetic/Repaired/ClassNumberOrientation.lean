module

public import blessed.SptCM.CM.ClassPolynomials
public import blessed.SptCM.Literature.RolenLiterature

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# I22: ordinary class number and the four level-six orientations

This module uses the pinned class-number part of E8.  E8 supplies (i) the
standard reduced-form/proper-ideal-class equivalence for the canonical
quadratic order and (ii) genuine simply transitive ideal-class actions.  The
four cardinality equalities are deductions, not fields of an interface.

The still-unresolved source/application gap is explicit: callers must produce
the four E8 actions on the concrete quotients `orientedForms n r`.  The current
paper explains these as the four choices of primes above `2` and `3`, but the
completion register says that an exact cited theorem with these conventions is
still required.
-/

namespace SptCM
namespace Arithmetic.Repaired

noncomputable section

open RolenLiterature

/-- The ordinary ideal-class number of the concrete order
`ℤ[(1 + √(-n))/2]`. -/
@[expose]
def ordinaryIdealClassNumber (n : ℕ) [IsDomain (NegativeQuadraticOrder n)] : ℕ :=
  Nat.card (ClassGroup (NegativeQuadraticOrder n))

/-- The exact I22 conclusion. -/
@[expose]
def ClassCountSpec (n : ℕ) : Prop :=
  ∃ domain : IsDomain (NegativeQuadraticOrder n),
    negativeClassNumber n = @ordinaryIdealClassNumber n domain ∧
      Nat.card (orientedForms n 1) = negativeClassNumber n ∧
      Nat.card (orientedForms n 11) = negativeClassNumber n ∧
      Nat.card (orientedForms n 5) = negativeClassNumber n ∧
      Nat.card (orientedForms n 7) = negativeClassNumber n

/-- Simple transitivity produces a bijection from the ideal-class group by
choosing one base point. -/
theorem equiv_of_E8IdealClassAction
    {R X : Type*} [CommRing R] [IsDomain R]
    (act : ClassGroup R → X → X) (h : E8IdealClassAction act) :
    Nonempty (ClassGroup R ≃ X) := by
  obtain ⟨x⟩ := h.2.1
  refine ⟨Equiv.ofBijective (fun g => act g x) ?_⟩
  constructor
  · intro a b hab
    obtain ⟨g, hg, huniq⟩ := h.2.2 x (act a x)
    have ha : a = g := huniq a rfl
    have hb : b = g := huniq b hab.symm
    exact ha.trans hb.symm
  · intro y
    obtain ⟨g, hg, _⟩ := h.2.2 x y
    exact ⟨g, hg⟩

/-- Consequently an E8 action gives the orientation count. -/
theorem orientation_count_of_E8
    {n r : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    [Finite (ClassGroup R)]
    (act : ClassGroup R → orientedForms n r → orientedForms n r)
    (hE8 : E8IdealClassAction act) :
    Nat.card (orientedForms n r) = Nat.card (ClassGroup R) := by
  obtain ⟨e⟩ := equiv_of_E8IdealClassAction act hE8
  exact (Nat.card_congr e).symm

/-- In the paper's range, `-n` is a fundamental discriminant in the
odd-discriminant sense used by the pinned E8 theorem. -/
theorem neg_isFundamentalDiscr
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23) :
    IsNegativeFundamentalDiscriminant n := by
  exact ⟨hsquarefree, by omega⟩

/-- The pinned reduced-form theorem identifies the existing reduced-form count
with the ordinary ideal-class number. -/
theorem reduced_count_of_E8
    {n : ℕ} [IsDomain (NegativeQuadraticOrder n)]
    [Finite (ClassGroup (NegativeQuadraticOrder n))]
    (hfund : IsNegativeFundamentalDiscriminant n)
    (hE8 : E8ReducedFormClassification n) :
    negativeClassNumber n = ordinaryIdealClassNumber n := by
  obtain ⟨e⟩ := hE8 hfund
  calc
    negativeClassNumber n = Nat.card (ReducedFormClasses n) := by
      unfold negativeClassNumber
      exact Fintype.card_eq_nat_card
    _ = Nat.card (ClassGroup (NegativeQuadraticOrder n)) := (Nat.card_congr e).symm
    _ = ordinaryIdealClassNumber n := rfl

/-- I22 derived from the two exact E8 outputs.  No cardinality equality occurs
among the hypotheses. -/
theorem classCountSpec_of_E8
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    [IsDomain (NegativeQuadraticOrder n)]
    [Finite (ClassGroup (NegativeQuadraticOrder n))]
    (hforms : E8ReducedFormClassification n)
    (act1 : ClassGroup (NegativeQuadraticOrder n) → orientedForms n 1 → orientedForms n 1)
    (act11 : ClassGroup (NegativeQuadraticOrder n) → orientedForms n 11 → orientedForms n 11)
    (act5 : ClassGroup (NegativeQuadraticOrder n) → orientedForms n 5 → orientedForms n 5)
    (act7 : ClassGroup (NegativeQuadraticOrder n) → orientedForms n 7 → orientedForms n 7)
    (hact1 : E8IdealClassAction act1)
    (hact11 : E8IdealClassAction act11)
    (hact5 : E8IdealClassAction act5)
    (hact7 : E8IdealClassAction act7) :
    ClassCountSpec n := by
  have hfund := neg_isFundamentalDiscr hsquarefree hmod
  have hred : negativeClassNumber n = ordinaryIdealClassNumber n :=
    reduced_count_of_E8 hfund hforms
  have h1 :
      Nat.card (orientedForms n 1) = ordinaryIdealClassNumber n := by
    simpa [ordinaryIdealClassNumber] using orientation_count_of_E8 act1 hact1
  have h11 :
      Nat.card (orientedForms n 11) = ordinaryIdealClassNumber n := by
    simpa [ordinaryIdealClassNumber] using orientation_count_of_E8 act11 hact11
  have h5 :
      Nat.card (orientedForms n 5) = ordinaryIdealClassNumber n := by
    simpa [ordinaryIdealClassNumber] using orientation_count_of_E8 act5 hact5
  have h7 :
      Nat.card (orientedForms n 7) = ordinaryIdealClassNumber n := by
    simpa [ordinaryIdealClassNumber] using orientation_count_of_E8 act7 hact7
  exact ⟨inferInstance, hred, h1.trans hred.symm, h11.trans hred.symm,
    h5.trans hred.symm, h7.trans hred.symm⟩

/-- The existing elementary estimate now bounds the ordinary class number. -/
theorem ordinaryIdealClassNumber_lt
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    [IsDomain (NegativeQuadraticOrder n)]
    (hcount : ClassCountSpec n) :
    ordinaryIdealClassNumber n < n := by
  obtain ⟨domain, hred, _⟩ := hcount
  have hred' : negativeClassNumber n = ordinaryIdealClassNumber n := by
    simpa only using hred
  rw [← hred']
  exact class_number_bound hsquarefree hmod

end

end Arithmetic.Repaired
end SptCM
