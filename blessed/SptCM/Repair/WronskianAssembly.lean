module

public import blessed.SptCM.CM.Repaired.I16Reduction
public import blessed.SptCM.Lemmas.Polynomial

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Wronskian assembly for the actual descended class polynomials

This file contains the final algebraic implication used after the geometric
CM argument has proved separation.  It is stated for the genuine
coefficient-descended polynomials of `ActualClassPolynomialSpec`, rather than
for arbitrary polynomial families.
-/

namespace SptCM.Repair

noncomputable section

open Polynomial
open SptCM.CM.Repaired

/-- Coprimality of the two actual coefficient reductions, together with the
paper's positive degree bound, forces their Wronskian to be nonzero.

The proof uses only monicity and the exact degree `2h`, both already derived
from the honest complex CM root products. -/
theorem actualClassPolynomials_wronskian_ne_zero
    {n h ℓ : ℕ} [Fact ℓ.Prime]
    {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)
    (h6 : IsUnit (6 : ZMod ℓ))
    (hcop : IsCoprime
      (D.actualReducedClassPolynomials ℓ h6).1
      (D.actualReducedClassPolynomials ℓ h6).2)
    (hdegreePos : 0 < 2 * h)
    (hdegreeLt : 2 * h < ℓ) :
    SptCM.wronskianObstruction
      (D.actualReducedClassPolynomials ℓ h6).1
      (D.actualReducedClassPolynomials ℓ h6).2 ≠ 0 := by
  apply SptCM.wronskianObstruction_ne_zero_zmod
    (Fact.out : ℓ.Prime) hcop
    (D.actualReducedClassPolynomials_monic ℓ h6).1
  · rw [(D.actualReducedClassPolynomials_degrees ℓ h6).1]
    exact hdegreePos
  · rw [(D.actualReducedClassPolynomials_degrees ℓ h6).1]
    exact hdegreeLt

end

end SptCM.Repair
