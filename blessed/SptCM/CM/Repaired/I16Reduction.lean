module

public import blessed.SptCM.CM.Repaired.I16Coordinates
public import blessed.SptCM.Repair.CMPolynomialReduction

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Coefficient reduction of the sound actual class-polynomial descent

Only the descended coefficients are reduced.  The algebraic CM roots are
never asserted to lie in `ℤ[1/6]` or in the prime field.
-/

namespace SptCM.CM.Repaired

noncomputable section

open Polynomial

namespace ActualClassPolynomialSpec

variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)


/-- The sound coefficient descent, viewed as the generic integral polynomial
pair used by the algebraic-closure reduction criterion. -/
@[expose]
def integralPolynomialPair : SptCM.IntegralOrientedClassPolynomials n where
  numerator := D.A
  denominator := D.B
  numerator_monic := D.monicA
  denominator_monic := D.monicB

/-- I17 for the actual descended coefficient pair: reduction is
coefficientwise and non-coprimality is equivalent to a common root over an
algebraic closure.  No root is asserted to lie in the prime field. -/
theorem actualRootReductionSpec
    {ℓ : ℕ} [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    SptCM.Repair.RootReductionSpec D.integralPolynomialPair h6 :=
  SptCM.Repair.rootReductionSpec_of_prime D.integralPolynomialPair h6

/-- Coefficientwise reductions of the sound descended numerator and
 denominator polynomials at a prime away from six. -/
@[expose]
def actualReducedClassPolynomials
    (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ)) :
    (ZMod ℓ)[X] × (ZMod ℓ)[X] :=
  (D.A.map (SptCM.awaySixReduction ℓ h6),
    D.B.map (SptCM.awaySixReduction ℓ h6))

/-- The descended numerator has the same degree `2h` as the actual complex
root product. -/
theorem A_natDegree : D.A.natDegree = 2 * h := by
  have hmap : (D.A.map SptCM.awaySixToComplex).natDegree = D.A.natDegree :=
    D.monicA.natDegree_map _
  rw [D.mapA] at hmap
  change C.actualNumeratorPolynomial.natDegree = D.A.natDegree at hmap
  rw [C.actual_class_polynomials_natDegree.1] at hmap
  exact hmap.symm

/-- The descended denominator has the same degree `2h`. -/
theorem B_natDegree : D.B.natDegree = 2 * h := by
  have hmap : (D.B.map SptCM.awaySixToComplex).natDegree = D.B.natDegree :=
    D.monicB.natDegree_map _
  rw [D.mapB] at hmap
  change C.actualDenominatorPolynomial.natDegree = D.B.natDegree at hmap
  rw [C.actual_class_polynomials_natDegree.2] at hmap
  exact hmap.symm

/-- Reduction at a good prime preserves both monic degrees. -/
theorem actualReducedClassPolynomials_degrees
    (ℓ : ℕ) [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (D.actualReducedClassPolynomials ℓ h6).1.natDegree = 2 * h ∧
      (D.actualReducedClassPolynomials ℓ h6).2.natDegree = 2 * h := by
  constructor
  · change (D.A.map (SptCM.awaySixReduction ℓ h6)).natDegree = 2 * h
    rw [D.monicA.natDegree_map, D.A_natDegree]
  · change (D.B.map (SptCM.awaySixReduction ℓ h6)).natDegree = 2 * h
    rw [D.monicB.natDegree_map, D.B_natDegree]

/-- Both reduced polynomials remain monic. -/
theorem actualReducedClassPolynomials_monic
    (ℓ : ℕ) [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) :
    (D.actualReducedClassPolynomials ℓ h6).1.Monic ∧
      (D.actualReducedClassPolynomials ℓ h6).2.Monic :=
  ⟨D.monicA.map _, D.monicB.map _⟩

end ActualClassPolynomialSpec

end

end SptCM.CM.Repaired
