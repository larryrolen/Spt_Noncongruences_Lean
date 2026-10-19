import blessed.SptCM.CM.Repaired.HauptmodulCoordinate
import blessed.SptCM.CM.ClassPolynomials

/-!
# The actual CM points and Hauptmodul values

This file removes the arbitrary coordinate functions from the CM-polynomial
construction.  A raw positive definite form `[a,b,c]` of discriminant `-n`
has the canonical point

`(-b + i * sqrt n) / (2a)`.

A modular function which is invariant under the concrete `Γ₀(6)`
change-of-variables relation therefore gives a well-defined function on the
actual quotient `orientedForms n r`.  Invariance is the only modular-curve
input; the quotient descent is proved here.
-/

namespace SptCM.CM.Repaired

noncomputable section

/-- The canonical complex CM point attached to a raw oriented quadratic form. -/
def rawCMPoint {n r : ℕ} (Q : RawOrientedForm n r) : ℂ :=
  ((-(Q.1.b : ℂ)) + Complex.I * Real.sqrt n) / (2 * (Q.1.a : ℂ))

/-- The imaginary part of the canonical CM point. -/
theorem rawCMPoint_im {n r : ℕ} (Q : RawOrientedForm n r) :
    (rawCMPoint Q).im = Real.sqrt n / (2 * Q.1.a) := by
  have haZ : Q.1.a ≠ 0 := ne_of_gt Q.2.2.1
  have haR : (Q.1.a : ℝ) ≠ 0 := by exact_mod_cast haZ
  rw [rawCMPoint, Complex.div_im]
  simp
  field_simp

/-- In the paper's positive-discriminant range, the canonical point lies in
`ℍ`.  Positivity of `a` comes from the definition of `rawOrientedForms`. -/
theorem rawCMPoint_im_pos {n r : ℕ} (hn : 0 < n)
    (Q : RawOrientedForm n r) : 0 < (rawCMPoint Q).im := by
  rw [rawCMPoint_im]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha : 0 < Q.1.a := Q.2.2.1
  exact div_pos hsqrt (by positivity)

/-- The actual upper-half-plane CM point of a raw oriented form. -/
def rawCMUpperHalfPlane {n r : ℕ} (hn : 0 < n)
    (Q : RawOrientedForm n r) : UpperHalfPlane :=
  ⟨rawCMPoint Q, rawCMPoint_im_pos hn Q⟩

/-- Values of a function on raw CM points are invariant under one concrete
`Γ₀(6)` change of variables.  This is the exact hypothesis needed for descent,
not an arbitrary function on the quotient. -/
def RawCMValueInvariant {n r : ℕ} (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ (hn : 0 < n) (Q Q' : RawOrientedForm n r),
    gammaZeroSixRelated n r Q Q' →
      F (rawCMUpperHalfPlane hn Q) = F (rawCMUpperHalfPlane hn Q')

/-- One-step invariance extends to the equivalence closure defining the actual
orientation classes. -/
theorem rawCMValue_eq_of_eqvGen {n r : ℕ} (F : UpperHalfPlane → ℂ)
    (hF : RawCMValueInvariant (n := n) (r := r) F) (hn : 0 < n)
    {Q Q' : RawOrientedForm n r}
    (h : Relation.EqvGen (gammaZeroSixRelated n r) Q Q') :
    F (rawCMUpperHalfPlane hn Q) = F (rawCMUpperHalfPlane hn Q') := by
  exact Relation.EqvGen.recOn h
    (fun x y hxy => hF hn x y hxy)
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)

/-- The value induced on the actual quotient of oriented forms. -/
def orientedCMValue {n r : ℕ} (F : UpperHalfPlane → ℂ)
    (hF : RawCMValueInvariant (n := n) (r := r) F) (hn : 0 < n) :
    orientedForms n r → ℂ :=
  Quotient.lift
    (fun Q : RawOrientedForm n r => F (rawCMUpperHalfPlane hn Q))
    (fun _ _ h => rawCMValue_eq_of_eqvGen F hF hn h)

/-- Evaluation on a represented class is definitionally the value at its
canonical CM point. -/
@[simp] theorem orientedCMValue_mk {n r : ℕ} (F : UpperHalfPlane → ℂ)
    (hF : RawCMValueInvariant (n := n) (r := r) F) (hn : 0 < n)
    (Q : RawOrientedForm n r) :
    orientedCMValue F hF hn (Quotient.mk'' Q) =
      F (rawCMUpperHalfPlane hn Q) := rfl

/-- Rolen's genuine eta-quotient value on the actual oriented form classes. -/
def actualOrientedHauptmodulValue {n r : ℕ}
    (hInv : RawCMValueInvariant (n := n) (r := r) analyticHauptmodul) (hn : 0 < n) :
    orientedForms n r → ℂ :=
  orientedCMValue analyticHauptmodul hInv hn

/-- The genuine value has the literal eta-quotient formula at every raw
representative. -/
@[simp] theorem actualOrientedHauptmodulValue_mk {n r : ℕ}
    (hInv : RawCMValueInvariant (n := n) (r := r) analyticHauptmodul) (hn : 0 < n)
    (Q : RawOrientedForm n r) :
    actualOrientedHauptmodulValue hInv hn (Quotient.mk'' Q) =
      analyticHauptmodul (rawCMUpperHalfPlane hn Q) := rfl

end

end SptCM.CM.Repaired
