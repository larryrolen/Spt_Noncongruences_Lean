module

public import blessed.SptCM.Analytic.Repaired.EulerProducts
public import blessed.SptCM.Analytic.Repaired.PairingBorcherds
public import blessed.SptCM.Analytic.Repaired.CuspWeylVectors
public import blessed.SptCM.CM.ActualClassPolynomials
public import blessed.SptCM.CM.Repaired.I16Coordinates
public import blessed.SptCM.CM.Repaired.I16Reduction
public import blessed.SptCM.Repair.I21ActualLaurentModel
public import Mathlib.RingTheory.HahnSeries.HEval
public import Mathlib.Algebra.Polynomial.Reverse

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# I12: the normalized Borcherds product

Unlike the former `NormalizedProductApplication` interface, this file uses
the actual Laurent-series evaluation of the class polynomials and the actual
canonical stabilized Euler products.  E5 is applied with its expansion
predicate fixed to that Euler quotient; E7's compact-curve laws are kept
separate from the paper-specific sign and root-product computations.
-/

namespace SptCM.Analytic.Repaired

open SptCM.RolenLiterature
open Polynomial

/-- The four local orientations occurring in the level-six Heegner divisor. -/
inductive I12Orientation
  | one | eleven | five | seven
  deriving DecidableEq

/-- The residue represented by an orientation. -/
@[expose]
def I12Orientation.residue : I12Orientation → Fin 12
  | .one => 1
  | .eleven => 11
  | .five => 5
  | .seven => 7

/-- The sign with which an oriented CM divisor occurs. -/
@[expose]
def I12Orientation.sign : I12Orientation → ℤ
  | .one | .eleven => 1
  | .five | .seven => -1

/-- A divisor supported on the four oriented CM families. -/
abbrev I12Divisor := I12Orientation → ℤ

/-- The divisor read directly from the coefficient at the unique negative
index of the vector-valued input. -/
@[expose]
def heegnerDivisorFromSeries (n : ℕ) (V : ℤ → Fin 12 → ℤ) : I12Divisor :=
  fun o => V (-(n : ℤ)) o.residue

/-- The displayed signed Heegner divisor
`D_(n,1)+D_(n,11)-D_(n,5)-D_(n,7)`. -/
@[expose]
def signedHeegnerDivisor : I12Divisor := I12Orientation.sign

/-- I12: the actual I10 principal part gives all four Heegner multiplicities,
including their signs, without an application predicate. -/
theorem prop_i12_heegner_divisor
    {Form : Type*} [SMul ℂ Form] {E : EtaJGeneratorBasis Form}
    {n : ℕ} {F : FourComponentInput Form}
    (hn : 0 < n) (hF : VectorInputSpec E n F) :
    heegnerDivisorFromSeries n F.vectorSeries = signedHeegnerDivisor := by
  funext o
  have h := hF.integralPrincipalPart (-(n : ℤ)) (by omega) o.residue
  simp only [heegnerDivisorFromSeries] at h ⊢
  rw [h]
  cases o <;>
    simp [signedHeegnerDivisor, I12Orientation.sign,
      I12Orientation.residue, chiTwelveResidue]

/-- The canonical embedding of `ℤ[1/6]` into `ℚ`. -/
@[expose]
noncomputable def awaySixToRat : SptCM.AwaySix →+* ℚ :=
  Localization.awayLift (Int.castRingHom ℚ) 6 (by norm_num)

/-- The actual Laurent-series evaluation of `A_n(t)/B_n(t)`.  The
coefficient polynomials come from a sound descent specification for the
genuine complex root products, and substitution is Mathlib's `aeval`. -/
@[expose]
noncomputable def actualClassPolynomialLaurentQuotient
    {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (t : LaurentSeries ℚ) : LaurentSeries ℚ :=
  Polynomial.aeval t (D.A.map awaySixToRat) /
    Polynomial.aeval t (D.B.map awaySixToRat)

/-- The actual stabilized Euler quotient attached to the scalar series of the
I10 input.  These are precisely the canonical products constructed in I14. -/
@[expose]
noncomputable def actualBorcherdsEulerQuotient {Form : Type*}
    (F : FourComponentInput Form) : LaurentSeries ℚ :=
  ((SptCM.Repair.eulerProductPlus F.scalarSeries : PowerSeries ℚ) :
      LaurentSeries ℚ) /
    ((SptCM.Repair.eulerProductMinus F.scalarSeries : PowerSeries ℚ) :
      LaurentSeries ℚ)

/-- The exact integral Euler-product Hauptmodul, base-changed to `ℚ` for
the characteristic-zero class-polynomial quotient. -/
@[expose]
noncomputable def actualRationalHauptmodulLaurent : LaurentSeries ℚ :=
  HahnSeries.map SptCM.Repair.hauptmodulFormalLaurent (Int.castRingHom ℚ)

/-- The rational base change retains the exact principal part
`q⁻¹ - 5 + O(q)`. -/
theorem actualRationalHauptmodulLaurent_principalPart :
    SptCM.Repair.HasHauptmodulPrincipalPart
      actualRationalHauptmodulLaurent := by
  rcases SptCM.Repair.hauptmodulFormalLaurent_principalPart with
    ⟨hneg, hzero, hbelow⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [actualRationalHauptmodulLaurent, HahnSeries.map_coeff] using
      congrArg (fun x : ℤ => (x : ℚ)) hneg
  · simpa [actualRationalHauptmodulLaurent, HahnSeries.map_coeff] using
      congrArg (fun x : ℤ => (x : ℚ)) hzero
  · intro z hz
    rw [actualRationalHauptmodulLaurent, HahnSeries.map_coeff, hbelow z hz]
    simp

/-- A Laurent series over a field with Hauptmodul principal part has
reciprocal of strictly positive order. -/
private theorem inverse_orderTop_pos_of_principalPart
    {K : Type*} [Field K] {t : LaurentSeries K}
    (h : SptCM.Repair.HasHauptmodulPrincipalPart t) :
    0 < t⁻¹.orderTop := by
  have ht : t ≠ 0 := SptCM.Repair.hauptmodul_ne_zero h
  have hle : (-1 : ℤ) ≤ t.order := by
    apply (HahnSeries.le_order_iff_forall ht).2
    exact h.2.2
  have hge : t.order ≤ (-1 : ℤ) := by
    apply HahnSeries.order_le_of_coeff_ne_zero
    rw [h.1]
    exact one_ne_zero
  have hord : t.order = (-1 : ℤ) := le_antisymm hge hle
  have htinv : t⁻¹ ≠ 0 := inv_ne_zero ht
  have hmul := HahnSeries.order_mul ht htinv
  rw [mul_inv_cancel₀ ht, hord] at hmul
  have hone : (1 : LaurentSeries K).order = 0 := by simp
  rw [hone] at hmul
  have hinvOrder : t⁻¹.order = (1 : ℤ) := by omega
  apply HahnSeries.zero_lt_orderTop_of_order
  rw [hinvOrder]
  norm_num

/-! ### Leading normalization in Laurent series -/

/-- Evaluating a polynomial after embedding it in the power-series ring
agrees with direct evaluation in Hahn series. -/
private lemma heval_coe_polynomial
    {K : Type*} [Field K] (x : HahnSeries ℤ K)
    (hx : 0 < x.orderTop) (p : K[X]) :
    PowerSeries.heval x (p : PowerSeries K) =
      Polynomial.eval₂ HahnSeries.C x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.coe_add, map_add, hp, hq,
        Polynomial.eval₂_add]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.coe_mul, Polynomial.coe_pow,
        Polynomial.coe_C, Polynomial.coe_X]
      rw [map_mul, map_pow, PowerSeries.heval_C,
        PowerSeries.heval_X x hx, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_X]
      have hC : a • (1 : HahnSeries ℤ K) = HahnSeries.C a := by
        ext z
        simp [HahnSeries.C_apply, HahnSeries.coeff_single]
      rw [hC]

/-- Equal-degree monic polynomials evaluated at a Laurent series with a
simple pole have quotient constant coefficient one.  The proof reverses the
polynomials and evaluates the resulting unit power series at `t⁻¹`. -/
private lemma monic_equalDegree_eval₂_quotient_coeff_zero
    {K : Type*} [Field K] (t : HahnSeries ℤ K)
    (ht : t ≠ 0) (hinv : 0 < t⁻¹.orderTop)
    (p q : K[X]) (hp : p.Monic) (hq : q.Monic)
    (hdeg : p.natDegree = q.natDegree) :
    (Polynomial.eval₂ HahnSeries.C t p /
      Polynomial.eval₂ HahnSeries.C t q).coeff 0 = 1 := by
  let _ : Invertible t := invertibleOfNonzero ht
  have hinvOf : ⅟ t = t⁻¹ := invOf_eq_inv t
  have hqcc : PowerSeries.constantCoeff (q.reverse : PowerSeries K) ≠ 0 := by
    simp [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
      hq.leadingCoeff]
  have hpreverse :
      PowerSeries.heval t⁻¹ (p.reverse : PowerSeries K) =
        Polynomial.eval₂ HahnSeries.C t⁻¹ p.reverse :=
    heval_coe_polynomial t⁻¹ hinv p.reverse
  have hqreverse :
      PowerSeries.heval t⁻¹ (q.reverse : PowerSeries K) =
        Polynomial.eval₂ HahnSeries.C t⁻¹ q.reverse :=
    heval_coe_polynomial t⁻¹ hinv q.reverse
  have hp_eval :
      Polynomial.eval₂ HahnSeries.C t p =
        Polynomial.eval₂ HahnSeries.C t⁻¹ p.reverse * t ^ p.natDegree := by
    simpa [hinvOf] using
      (Polynomial.eval₂_reverse_mul_pow HahnSeries.C t p).symm
  have hq_eval :
      Polynomial.eval₂ HahnSeries.C t q =
        Polynomial.eval₂ HahnSeries.C t⁻¹ q.reverse * t ^ q.natDegree := by
    simpa [hinvOf] using
      (Polynomial.eval₂_reverse_mul_pow HahnSeries.C t q).symm
  rw [hp_eval, hq_eval, ← hdeg]
  have hqrne : Polynomial.eval₂ HahnSeries.C t⁻¹ q.reverse ≠ 0 := by
    rw [← hqreverse]
    intro hz
    have hprod :
        PowerSeries.heval t⁻¹
            ((q.reverse : PowerSeries K) *
              (q.reverse : PowerSeries K)⁻¹) = 0 := by
      rw [map_mul, hz, zero_mul]
    rw [PowerSeries.mul_inv_cancel (q.reverse : PowerSeries K) hqcc,
      map_one] at hprod
    exact one_ne_zero hprod
  rw [mul_div_mul_right _ _ (pow_ne_zero _ ht)]
  rw [div_eq_mul_inv, ← hpreverse, ← hqreverse]
  have hmapinv :
      (PowerSeries.heval t⁻¹ (q.reverse : PowerSeries K))⁻¹ =
        PowerSeries.heval t⁻¹ ((q.reverse : PowerSeries K)⁻¹) := by
    have hqrne_heval :
        PowerSeries.heval t⁻¹ (q.reverse : PowerSeries K) ≠ 0 := by
      rw [hqreverse]
      exact hqrne
    apply (mul_left_cancel₀ (a := PowerSeries.heval t⁻¹
      (q.reverse : PowerSeries K)) hqrne_heval)
    rw [mul_inv_cancel₀ hqrne_heval, ← map_mul,
      PowerSeries.mul_inv_cancel (q.reverse : PowerSeries K) hqcc, map_one]
  rw [hmapinv, ← map_mul]
  rw [PowerSeries.coeff_heval_zero]
  simp [map_mul, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
    hp.leadingCoeff, hq.leadingCoeff]

/-- The actual class-polynomial quotient has Laurent leading value one.
Monicity and equal degree come from the genuine descended root products;
the two assumptions on `t` are the formal content of its simple principal
part at the cusp. -/
theorem actualClassPolynomialLaurentQuotient_coeff_zero
    {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (t : LaurentSeries ℚ) (ht : t ≠ 0)
    (hinv : 0 < t⁻¹.orderTop) :
    (actualClassPolynomialLaurentQuotient D t).coeff 0 = 1 := by
  unfold actualClassPolynomialLaurentQuotient
  have hmonicA : (D.A.map awaySixToRat).Monic := D.monicA.map _
  have hmonicB : (D.B.map awaySixToRat).Monic := D.monicB.map _
  have hdeg :
      (D.A.map awaySixToRat).natDegree =
        (D.B.map awaySixToRat).natDegree := by
    rw [D.monicA.natDegree_map, D.monicB.natDegree_map,
      D.A_natDegree, D.B_natDegree]
  have hC :
      HahnSeries.C =
        algebraMap ℚ (LaurentSeries ℚ) := by
    ext a z
    simp
  simpa [Polynomial.aeval_def, ← hC] using
    monic_equalDegree_eval₂_quotient_coeff_zero
      t ht hinv (D.A.map awaySixToRat) (D.B.map awaySixToRat)
      hmonicA hmonicB hdeg

/-- For the exact rational Euler-product Hauptmodul, the class-polynomial
Laurent quotient has leading coefficient one with no normalization
assumption. -/
theorem actualClassPolynomialLaurentQuotient_leading_normalization
    {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    (actualClassPolynomialLaurentQuotient
      D actualRationalHauptmodulLaurent).coeff 0 = 1 := by
  apply actualClassPolynomialLaurentQuotient_coeff_zero
  · exact SptCM.Repair.hauptmodul_ne_zero
      actualRationalHauptmodulLaurent_principalPart
  · exact inverse_orderTop_pos_of_principalPart
      actualRationalHauptmodulLaurent_principalPart

/-- Root-divisor of the actual class-polynomial quotient.  It is computed
from which of the four concrete products a root factor belongs to. -/
@[expose]
def actualClassPolynomialRootDivisor : I12Divisor
  | .one | .eleven => 1
  | .five | .seven => -1

/-- I12: the two actual root products have divisor
`D_(n,1)+D_(n,11)-D_(n,5)-D_(n,7)`, factor by factor. -/
theorem actualClassPolynomialRootDivisor_eq_signed {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (_D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    actualClassPolynomialRootDivisor = signedHeegnerDivisor := by
  funext o
  cases o <;> rfl

/-- The canonical Euler numerator and denominator both have constant
coefficient one.  This is the genuine part of the leading-normalization
calculation already available from the constructed stabilized products. -/
theorem canonicalEulerProducts_leading_normalization {Form : Type*}
    (F : FourComponentInput Form) :
    PowerSeries.coeff 0
        (SptCM.Repair.eulerProductPlus F.scalarSeries : PowerSeries ℚ) = 1 ∧
      PowerSeries.coeff 0
        (SptCM.Repair.eulerProductMinus F.scalarSeries : PowerSeries ℚ) = 1 := by
  have h := SptCM.Repair.eulerProducts_spec (R := ℚ) F.scalarSeries
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- The quotient of the two canonical Euler products is normalized already
in `ℚ[[q]]`: its constant coefficient is one. -/
theorem canonicalEulerPowerSeriesQuotient_leading_normalization
    {Form : Type*} (F : FourComponentInput Form) :
    PowerSeries.constantCoeff
        ((SptCM.Repair.eulerProductPlus F.scalarSeries : PowerSeries ℚ) *
          (SptCM.Repair.eulerProductMinus F.scalarSeries :
            PowerSeries ℚ)⁻¹) =
      1 := by
  obtain ⟨hplus, hminus⟩ :=
    canonicalEulerProducts_leading_normalization F
  rw [map_mul, PowerSeries.constantCoeff_inv]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hplus,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hminus]
  norm_num

/-- The same canonical Euler quotient is normalized after embedding from
power series into Laurent series. -/
theorem actualBorcherdsEulerQuotient_coeff_zero
    {Form : Type*} (F : FourComponentInput Form) :
    (actualBorcherdsEulerQuotient F).coeff 0 = 1 := by
  let P : PowerSeries ℚ :=
    SptCM.Repair.eulerProductPlus F.scalarSeries
  let M : PowerSeries ℚ :=
    SptCM.Repair.eulerProductMinus F.scalarSeries
  have hMconst : PowerSeries.constantCoeff M ≠ 0 := by
    have h := (canonicalEulerProducts_leading_normalization F).2
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    simp [M, h]
  have hMne : ((M : PowerSeries ℚ) : LaurentSeries ℚ) ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun f : LaurentSeries ℚ => f.coeff 0) hz
    have hcoeff :
        PowerSeries.coeff 0 M = 0 := by
      rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) M 0]
      exact hz0
    apply hMconst
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hcoeff
  have hmapinv :
      (((M : PowerSeries ℚ) : LaurentSeries ℚ))⁻¹ =
        (((M⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ)) := by
    apply (mul_left_cancel₀ (a :=
      ((M : PowerSeries ℚ) : LaurentSeries ℚ)) hMne)
    rw [mul_inv_cancel₀ hMne]
    rw [← map_mul, PowerSeries.mul_inv_cancel M hMconst, map_one]
  unfold actualBorcherdsEulerQuotient
  change
    ((((P : PowerSeries ℚ) : LaurentSeries ℚ) /
      ((M : PowerSeries ℚ) : LaurentSeries ℚ)).coeff 0) = 1
  rw [div_eq_mul_inv, hmapinv, ← map_mul]
  have hcoeff :=
    HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (P * M⁻¹) 0
  change
    ((HahnSeries.ofPowerSeries ℤ ℚ (P * M⁻¹)).coeff
      ((0 : ℕ) : ℤ)) = 1
  rw [hcoeff]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact canonicalEulerPowerSeriesQuotient_leading_normalization F

/-- I12 leading normalization on both sides: the exact class-polynomial
Laurent quotient and the canonical Borcherds Euler quotient each have
coefficient zero equal to one. -/
theorem i12_leading_normalization
    {Form : Type*} {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (F : FourComponentInput Form) :
    (actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent).coeff 0 = 1 ∧
      (actualBorcherdsEulerQuotient F).coeff 0 = 1 :=
  ⟨actualClassPolynomialLaurentQuotient_leading_normalization D,
    actualBorcherdsEulerQuotient_coeff_zero F⟩

/-- Predicted divisor read from the unique negative coefficient. -/
@[expose]
def actualPredictedHeegnerDivisor {Form : Type*} (n : ℕ) :
    FourComponentInput Form → I12Divisor :=
  fun F => heegnerDivisorFromSeries n F.vectorSeries

/-- E5 applied to the actual I10 input and the fixed canonical stabilized
Euler quotient.  The expansion predicate is no longer caller-selectable. -/
@[expose]
def actualI12BorcherdsModel {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (n : ℕ)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (divisor : LaurentSeries ℚ → I12Divisor)
    (unitary : LaurentSeries ℚ → Prop) :
    BorcherdsLiftModel (FourComponentInput Form) (LaurentSeries ℚ) I12Divisor where
  admissibleInput := VectorInputSpec E n
  lift := lift
  divisor := divisor
  predictedDivisor := actualPredictedHeegnerDivisor n
  hasUnitaryCharacter := unitary
  hasProductExpansion := fun F g => g = actualBorcherdsEulerQuotient F

/-- The source-faithful E5 consequence that is currently available: its lift
has the actual canonical stabilized Euler expansion.  This deliberately does
not identify the lift with the class-polynomial quotient; that requires the
missing internal divisor/rigidity/leading calculations, not an enlarged E7. -/
theorem actualI12Lift_eq_canonicalEulerQuotient
    {Form : Type*} [SMul ℂ Form] {n : ℕ}
    (E : EtaJGeneratorBasis Form)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (divisor : LaurentSeries ℚ → I12Divisor)
    (unitary : LaurentSeries ℚ → Prop)
    (hE5 : E5BruinierOno
      (actualI12BorcherdsModel E n lift divisor unitary))
    (F : FourComponentInput Form) (hF : VectorInputSpec E n F) :
    lift F = actualBorcherdsEulerQuotient F := by
  simpa [actualI12BorcherdsModel] using (hE5 F hF).2.2

/-- E5 and the actual negative Fourier coefficient determine the lift's
divisor, with no paper-specific divisor assertion stored in a record. -/
theorem actualI12Lift_divisor_eq_signed
    {Form : Type*} [SMul ℂ Form] {n : ℕ}
    (E : EtaJGeneratorBasis Form)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (divisor : LaurentSeries ℚ → I12Divisor)
    (unitary : LaurentSeries ℚ → Prop)
    (hE5 : E5BruinierOno
      (actualI12BorcherdsModel E n lift divisor unitary))
    (F : FourComponentInput Form) (hn : 0 < n)
    (hF : VectorInputSpec E n F) :
    divisor (lift F) = signedHeegnerDivisor := by
  have hdiv := (hE5 F hF).1
  change divisor (lift F) = actualPredictedHeegnerDivisor n F at hdiv
  rw [hdiv]
  exact prop_i12_heegner_divisor hn hF

/-! ### Explicit divisor-rigidity-normalization assembly

The following structure contains only geometric operations.  The general
rigidity and leading-value laws are quantified separately, so there is no
application object with a field equal to the desired product identity. -/

/-- Neutral operations on the meromorphic functions used in I12. -/
structure I12MeromorphicGeometry (Function Divisor CuspData Scalar : Type*) where
  divisor : Function → Divisor
  cuspData : Function → CuspData
  leadingValue : Function → Scalar

/-- Geometric interpretation of finite root products: evaluating the actual
class-polynomial quotient in the exact Hauptmodul has precisely the signed
root divisor computed from its numerator and denominator factors.  This is
quantified over every descended class-polynomial specification and does not
assume the final Borcherds-product identity. -/
@[expose]
def I12ClassPolynomialDivisorPrinciple
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ) : Prop :=
  ∀ {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (_D : SptCM.CM.Repaired.ActualClassPolynomialSpec C),
    G.divisor (actualClassPolynomialLaurentQuotient
      _D actualRationalHauptmodulLaurent) =
        actualClassPolynomialRootDivisor

/-- The finite CM roots are interior points, so the equal-degree
class-polynomial quotient has no cusp contribution.  As above, this is a
uniform geometric interpretation law, not the desired product equality. -/
@[expose]
def I12ClassPolynomialCuspPrinciple
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ) : Prop :=
  ∀ {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (_D : SptCM.CM.Repaired.ActualClassPolynomialSpec C),
    G.cuspData (actualClassPolynomialLaurentQuotient
      _D actualRationalHauptmodulLaurent) = 0

/-- General interpretation of Weyl vectors as cusp orders of a Borcherds
lift: vanishing at all four level-six cusps forces trivial cusp data. -/
@[expose]
def I12WeylCuspPrinciple
    {Form : Type*}
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (weylVector : FourComponentInput Form → ℕ → ℂ) : Prop :=
  ∀ F, (∀ c, IsLevelSixDivisor c → weylVector F c = 0) →
    G.cuspData (lift F) = 0

/-- The divisor of the genuine class-polynomial Laurent quotient is the
signed Heegner divisor.  The only boundary input is the uniform
root-product/divisor interpretation law; the Rolen-specific sign calculation
is internal. -/
theorem actualClassPolynomialLaurentQuotient_divisor_eq_signed
    {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ)
    (hClassDivisor : I12ClassPolynomialDivisorPrinciple G) :
    G.divisor (actualClassPolynomialLaurentQuotient
      D actualRationalHauptmodulLaurent) = signedHeegnerDivisor := by
  rw [hClassDivisor D]
  exact actualClassPolynomialRootDivisor_eq_signed D

/-- General compact-curve rigidity: two meromorphic functions with the same
horizontal divisor and cusp data differ by a scalar. -/
@[expose]
def I12DivisorRigidityPrinciple
    {Function Divisor CuspData Scalar : Type*}
    [Field Scalar] [Field Function] [Algebra Scalar Function]
    (G : I12MeromorphicGeometry Function Divisor CuspData Scalar) : Prop :=
  ∀ f g, G.divisor f = G.divisor g → G.cuspData f = G.cuspData g →
    ∃ c : Scalar, f = algebraMap Scalar Function c * g

/-- General compatibility of the leading value with scalar multiplication. -/
@[expose]
def I12LeadingValuePrinciple
    {Function Divisor CuspData Scalar : Type*}
    [Field Scalar] [Field Function] [Algebra Scalar Function]
    (G : I12MeromorphicGeometry Function Divisor CuspData Scalar) : Prop :=
  ∀ c : Scalar, ∀ f,
    G.leadingValue (algebraMap Scalar Function c * f) =
      c * G.leadingValue f

/-- Equal divisors and cusp data give a scalar multiple; equal normalized
leading values force that scalar to be one. -/
theorem eq_of_I12_divisor_rigidity_and_normalization
    {Function Divisor CuspData Scalar : Type*}
    [Field Scalar] [Field Function] [Algebra Scalar Function]
    (G : I12MeromorphicGeometry Function Divisor CuspData Scalar)
    (hRigidity : I12DivisorRigidityPrinciple G)
    (hLeading : I12LeadingValuePrinciple G)
    (f g : Function)
    (hdivisor : G.divisor f = G.divisor g)
    (hcusp : G.cuspData f = G.cuspData g)
    (hf : G.leadingValue f = 1)
    (hg : G.leadingValue g = 1) :
    f = g := by
  obtain ⟨c, hc⟩ := hRigidity f g hdivisor hcusp
  have hc_one : c = 1 := by
    have h := congrArg G.leadingValue hc
    rw [hLeading, hf, hg, mul_one] at h
    exact h.symm
  subst c
  simpa using hc

/-- I12 cusp rigidity derived from E6 rather than a cusp-equality
assumption.  The component calculation makes every Weyl vector vanish; the
two general interpretation laws turn this and the interior CM-root
calculation into equal divisor and cusp data, so compact-curve rigidity gives
a scalar multiple. -/
theorem i12_cusp_rigidity
    {Form V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V] {n h : ℕ}
    (E : EtaJGeneratorBasis Form)
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ)
    (F : FourComponentInput Form) (hF : VectorInputSpec E n F)
    (weylVector : FourComponentInput Form → ℕ → ℂ)
    (pairing : FourComponentInput Form → V →ₗ[ℂ] ℂ)
    (theta : Fin 12 → V) (eta : V) (normalization : ℂ → ℂ)
    (hE6 : E6BruinierSchwagenscheidt
      (componentWeylVectorModel (VectorInputSpec E n) weylVector pairing
        theta normalization))
    (heta : EtaComponentThetaIdentity theta eta)
    (hpairing : pairing F eta = 0)
    (hnormalization : normalization 0 = 0)
    (hClassDivisor : I12ClassPolynomialDivisorPrinciple G)
    (hClassCusp : I12ClassPolynomialCuspPrinciple G)
    (hWeylCusp : I12WeylCuspPrinciple G lift weylVector)
    (hliftDivisor : G.divisor (lift F) = signedHeegnerDivisor)
    (hRigidity : I12DivisorRigidityPrinciple G) :
    ∃ c : ℚ, lift F = algebraMap ℚ (LaurentSeries ℚ) c *
      actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent := by
  have hweyl : ∀ c, IsLevelSixDivisor c → weylVector F c = 0 :=
    componentWeylVectors_eq_zero (VectorInputSpec E n) weylVector pairing
      theta eta normalization hE6 heta F hF hpairing hnormalization
  have hliftCusp : G.cuspData (lift F) = 0 := hWeylCusp F hweyl
  have hclassCusp :
      G.cuspData (actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent) = 0 :=
    hClassCusp D
  have hclassDivisor :
      G.divisor (actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent) = signedHeegnerDivisor :=
    actualClassPolynomialLaurentQuotient_divisor_eq_signed
      D G hClassDivisor
  apply hRigidity
  · exact hliftDivisor.trans hclassDivisor.symm
  · exact hliftCusp.trans hclassCusp.symm

/-- The exact normalized I12 identity under general, source-faithful
geometric interpretation laws.  E5 supplies the lift divisor and canonical
Euler expansion; E6 and the component calculation supply vanishing Weyl
vectors; the root-product and Weyl interpretation principles supply the
divisor/cusp comparison; and both leading normalizations are derived
internally.  No desired equality or leading-value conclusion is assumed. -/
theorem actualClassPolynomialLaurentQuotient_eq_canonicalEulerQuotient
    {Form V : Type*} [SMul ℂ Form]
    [AddCommMonoid V] [Module ℂ V] {n h : ℕ}
    (E : EtaJGeneratorBasis Form)
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (unitary : LaurentSeries ℚ → Prop)
    (G : I12MeromorphicGeometry
      (LaurentSeries ℚ) I12Divisor I12Divisor ℚ)
    (hE5 : E5BruinierOno
      (actualI12BorcherdsModel E n lift G.divisor unitary))
    (F : FourComponentInput Form) (hn : 0 < n)
    (hF : VectorInputSpec E n F)
    (weylVector : FourComponentInput Form → ℕ → ℂ)
    (pairing : FourComponentInput Form → V →ₗ[ℂ] ℂ)
    (theta : Fin 12 → V) (eta : V) (normalization : ℂ → ℂ)
    (hE6 : E6BruinierSchwagenscheidt
      (componentWeylVectorModel (VectorInputSpec E n) weylVector pairing
        theta normalization))
    (heta : EtaComponentThetaIdentity theta eta)
    (hpairing : pairing F eta = 0)
    (hnormalization : normalization 0 = 0)
    (hRigidity : I12DivisorRigidityPrinciple G)
    (hLeading : I12LeadingValuePrinciple G)
    (hLeadingCoeff :
      ∀ f : LaurentSeries ℚ, G.leadingValue f = f.coeff 0)
    (hClassDivisor : I12ClassPolynomialDivisorPrinciple G)
    (hClassCusp : I12ClassPolynomialCuspPrinciple G)
    (hWeylCusp : I12WeylCuspPrinciple G lift weylVector) :
    actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent =
      actualBorcherdsEulerQuotient F := by
  have hliftDivisor : G.divisor (lift F) = signedHeegnerDivisor :=
    actualI12Lift_divisor_eq_signed E lift G.divisor unitary hE5 F hn hF
  have hliftEuler :
      lift F = actualBorcherdsEulerQuotient F :=
    actualI12Lift_eq_canonicalEulerQuotient
      E lift G.divisor unitary hE5 F hF
  have hliftLeading : G.leadingValue (lift F) = 1 := by
    rw [hLeadingCoeff, hliftEuler,
      actualBorcherdsEulerQuotient_coeff_zero]
  have hclassLeading :
      G.leadingValue (actualClassPolynomialLaurentQuotient
        D actualRationalHauptmodulLaurent) = 1 := by
    rw [hLeadingCoeff,
      actualClassPolynomialLaurentQuotient_leading_normalization D]
  obtain ⟨c, hc⟩ := i12_cusp_rigidity E D lift G F hF weylVector
    pairing theta eta normalization hE6 heta hpairing hnormalization
    hClassDivisor hClassCusp hWeylCusp hliftDivisor hRigidity
  have hc_one : c = 1 := by
    have hlead := congrArg G.leadingValue hc
    rw [hLeading, hliftLeading, hclassLeading, mul_one] at hlead
    exact hlead.symm
  subst c
  have heq : lift F = actualClassPolynomialLaurentQuotient
      D actualRationalHauptmodulLaurent := by
    simpa using hc
  rw [← heq]
  exact hliftEuler

end SptCM.Analytic.Repaired
