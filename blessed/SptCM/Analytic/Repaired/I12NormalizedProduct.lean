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
public import blessed.SptCM.Repair.LaurentTranscendence
public import blessed.SptCM.Analytic.Repaired.I12RationalRigidity
public import blessed.SptCM.Analytic.Repaired.I12UnitaryAnalytic

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

/-- The embedding of the rational function field in the genuine formal
Hauptmodul. Its simple pole proves transcendence, so this is an injective
algebra homomorphism, not an arbitrary interpretation of formal series. -/
@[expose]
noncomputable def rationalHauptmodulExpansion :
    RatFunc ℚ →+* LaurentSeries ℚ :=
  IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) (L := LaurentSeries ℚ)
    (g := (Polynomial.aeval actualRationalHauptmodulLaurent).toRingHom)
    (by
      exact transcendental_iff_injective.mp
        (SptCM.Repair.laurentSeries_transcendental_of_simple_pole
          actualRationalHauptmodulLaurent
          actualRationalHauptmodulLaurent_principalPart.1
          actualRationalHauptmodulLaurent_principalPart.2.2))

set_option maxHeartbeats 2000000 in
theorem rationalHauptmodulExpansion_polynomial (p : ℚ[X]) :
    rationalHauptmodulExpansion (algebraMap ℚ[X] (RatFunc ℚ) p) =
      Polynomial.aeval actualRationalHauptmodulLaurent p := by
  unfold rationalHauptmodulExpansion
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- Every class-polynomial quotient belongs to the rational function field. -/
theorem classPolynomialQuotient_is_rational {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) :
    ∃ r : RatFunc ℚ, rationalHauptmodulExpansion r =
      actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent := by
  refine ⟨algebraMap ℚ[X] (RatFunc ℚ) (D.A.map awaySixToRat) /
    algebraMap ℚ[X] (RatFunc ℚ) (D.B.map awaySixToRat), ?_⟩
  simp only [map_div₀, rationalHauptmodulExpansion_polynomial,
    actualClassPolynomialLaurentQuotient]

/-- The complete divisor of a single oriented CM family, retaining the
Hauptmodul coordinate of every point and its multiplicity. -/
@[expose]
noncomputable def orientedCMPointDivisor {n h : ℕ}
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h)
    (o : I12Orientation) (z : ℂ) : ℤ :=
  match o with
  | .one => (classPolynomial (fun i : C.orientation1.Index =>
      SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant1 C.n_pos
        (C.orientation1.classes i))).rootMultiplicity z
  | .eleven => (classPolynomial (fun i : C.orientation11.Index =>
      SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant11 C.n_pos
        (C.orientation11.classes i))).rootMultiplicity z
  | .five => (classPolynomial (fun i : C.orientation5.Index =>
      SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant5 C.n_pos
        (C.orientation5.classes i))).rootMultiplicity z
  | .seven => (classPolynomial (fun i : C.orientation7.Index =>
      SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant7 C.n_pos
        (C.orientation7.classes i))).rootMultiplicity z

@[expose]
noncomputable def fullHeegnerDivisor {n h : ℕ}
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h)
    (a : I12Divisor) (z : ℂ) : ℤ :=
  a .one * orientedCMPointDivisor C .one z +
    a .eleven * orientedCMPointDivisor C .eleven z +
    a .five * orientedCMPointDivisor C .five z +
    a .seven * orientedCMPointDivisor C .seven z

/-- Multiplicities of the actual numerator roots minus those of the actual
denominator roots. Different discriminants no longer receive the same divisor. -/
@[expose]
noncomputable def fullClassPolynomialDivisor {n h : ℕ}
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h) (z : ℂ) : ℤ :=
  (C.actualNumeratorPolynomial.rootMultiplicity z : ℤ) -
    (C.actualDenominatorPolynomial.rootMultiplicity z : ℤ)

theorem fullHeegnerDivisor_signed {n h : ℕ}
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h) :
    fullHeegnerDivisor C signedHeegnerDivisor = fullClassPolynomialDivisor C := by
  funext z
  simp only [fullHeegnerDivisor, signedHeegnerDivisor, I12Orientation.sign,
    one_mul, neg_one_mul, fullClassPolynomialDivisor,
    SptCM.CM.Repaired.ActualOrientedCMCoordinates.actualNumeratorPolynomial,
    SptCM.CM.Repaired.ActualOrientedCMCoordinates.actualDenominatorPolynomial,
    classPolynomial, Fintype.prod_sum_type]
  rw [Polynomial.rootMultiplicity_mul (by
    exact mul_ne_zero (classPolynomial_monic _).ne_zero (classPolynomial_monic _).ne_zero),
    Polynomial.rootMultiplicity_mul (by
      exact mul_ne_zero (classPolynomial_monic _).ne_zero (classPolynomial_monic _).ne_zero)]
  simp only [orientedCMPointDivisor, classPolynomial, Nat.cast_add,
    SptCM.CM.Repaired.ActualOrientedCMCoordinates.numeratorRoot,
    SptCM.CM.Repaired.ActualOrientedCMCoordinates.denominatorRoot]
  ring

/-- Interior divisors are functions of actual complex coordinates. Cusp
orders are real because a unitary character can have nonintegral exponents.
The compatibility law is needed only when every cusp order is zero. -/
structure I12MeromorphicGeometry where
  divisor : LaurentSeries ℚ → ℂ → ℤ
  cuspData : LaurentSeries ℚ → Fin 4 → ℝ
  analyticCuspOrders : ∀ f (R : I12UnitaryMeromorphicRealization f),
    cuspData f = R.cuspOrder
  analyticDivisor : ∀ f (R : I12UnitaryMeromorphicRealization f)
    (τ : UpperHalfPlane),
    divisor f (SptCM.CM.Repaired.analyticHauptmodul τ) =
      (meromorphicOrderAt R.toFun (τ : ℂ)).untop₀
  rationalDivisor : ∀ r : RatFunc ℚ, r ≠ 0 →
    cuspData (rationalHauptmodulExpansion r) = 0 →
    divisor (rationalHauptmodulExpansion r) = rationalFunctionDivisor r

/-- Explicit analytic descent input: a nonzero weight-zero meromorphic form
with unitary character and zero cusp orders on the compact genus-zero curve
is rational in its Hauptmodul. The analytic domain is fixed by convergent
expansions and actual meromorphic functions, rather than a caller-selected
predicate. This general descent theorem remains an explicit analytic input;
it involves no CM polynomials or target identity. -/
@[expose]
def I12GenusZeroDescentPrinciple (G : I12MeromorphicGeometry) : Prop :=
  ∀ f, HasI12UnitaryMeromorphicRealization f → G.cuspData f = 0 → f ≠ 0 →
    ∃ r : RatFunc ℚ, rationalHauptmodulExpansion r = f

/-- The finite CM roots are interior points, and the monic equal-degree
quotient has no zero or pole at any cusp. -/
@[expose]
def I12ClassPolynomialCuspPrinciple (G : I12MeromorphicGeometry) : Prop :=
  ∀ {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C),
    G.cuspData (actualClassPolynomialLaurentQuotient
      D actualRationalHauptmodulLaurent) = 0

@[expose]
def I12WeylCuspPrinciple {Form : Type*} (G : I12MeromorphicGeometry)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (weylVector : FourComponentInput Form → ℕ → ℂ) : Prop :=
  ∀ F, (∀ c, IsLevelSixDivisor c → weylVector F c = 0) → G.cuspData (lift F) = 0

/-- E5 with the full, discriminant-dependent Heegner divisor, applied only
after all Weyl vectors vanish so that the product has no cusp prefactor. -/
@[expose]
noncomputable def actualI12BorcherdsModel {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) {n h : ℕ}
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (divisor : LaurentSeries ℚ → ℂ → ℤ)
    (weylVector : FourComponentInput Form → ℕ → ℂ) :
    BorcherdsLiftModel (FourComponentInput Form) (LaurentSeries ℚ) (ℂ → ℤ) where
  admissibleInput := fun F => VectorInputSpec E n F ∧
    (∀ c, IsLevelSixDivisor c → weylVector F c = 0)
  lift := lift
  divisor := divisor
  predictedDivisor := fun F => fullHeegnerDivisor C
    (heegnerDivisorFromSeries n F.vectorSeries)
  hasUnitaryCharacter := HasI12UnitaryMeromorphicRealization
  hasProductExpansion := fun F g => g = actualBorcherdsEulerQuotient F

theorem actualI12Lift_divisor_eq_full {Form : Type*} [SMul ℂ Form] {n h : ℕ}
    (E : EtaJGeneratorBasis Form)
    (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (G : I12MeromorphicGeometry)
    (weylVector : FourComponentInput Form → ℕ → ℂ)
    (hE5 : E5BruinierOno (actualI12BorcherdsModel E C lift G.divisor weylVector))
    (F : FourComponentInput Form) (hn : 0 < n) (hF : VectorInputSpec E n F)
    (hweyl : ∀ c, IsLevelSixDivisor c → weylVector F c = 0) :
    G.divisor (lift F) = fullClassPolynomialDivisor C := by
  have hdiv := (hE5 F ⟨hF, hweyl⟩).1
  change G.divisor (lift F) =
    fullHeegnerDivisor C (heegnerDivisorFromSeries n F.vectorSeries) at hdiv
  rw [prop_i12_heegner_divisor hn hF, fullHeegnerDivisor_signed] at hdiv
  exact hdiv

theorem awaySixToRat_toComplex :
    (algebraMap ℚ ℂ).comp awaySixToRat = SptCM.awaySixToComplex := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (6 : ℤ))
  ext n
  simp [awaySixToRat, SptCM.awaySixToComplex]

/-- The class-polynomial divisor is derived from the full rational-function
divisor, rather than asserted using four orientation labels. -/
theorem classPolynomialQuotient_divisor {n h : ℕ}
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (G : I12MeromorphicGeometry) (hcusp : I12ClassPolynomialCuspPrinciple G) :
    G.divisor (actualClassPolynomialLaurentQuotient D
      actualRationalHauptmodulLaurent) = fullClassPolynomialDivisor C := by
  let p := D.A.map awaySixToRat
  let q := D.B.map awaySixToRat
  let r : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) p /
    algebraMap ℚ[X] (RatFunc ℚ) q
  have hr : rationalHauptmodulExpansion r =
      actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent := by
    simp only [r, p, q, map_div₀, rationalHauptmodulExpansion_polynomial,
      actualClassPolynomialLaurentQuotient]
  have hp : p ≠ 0 := (D.monicA.map awaySixToRat).ne_zero
  have hq : q ≠ 0 := (D.monicB.map awaySixToRat).ne_zero
  have hr0 : r ≠ 0 := div_ne_zero
    (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  rw [← hr, G.rationalDivisor r hr0 (hr ▸ hcusp D),
    rationalFunctionDivisor_div p q hp hq]
  simp only [p, q, Polynomial.map_map, awaySixToRat_toComplex, D.mapA, D.mapB]
  rfl

/-- Rigidity is proved for rational functions, with nonzero hypotheses and
full point divisors. It is no longer assumed for all formal Laurent series. -/
theorem eq_of_rational_divisors_and_normalization (G : I12MeromorphicGeometry)
    (f g : LaurentSeries ℚ)
    (hf : ∃ r : RatFunc ℚ, rationalHauptmodulExpansion r = f)
    (hg : ∃ r : RatFunc ℚ, rationalHauptmodulExpansion r = g)
    (hfcusp : G.cuspData f = 0) (hgcusp : G.cuspData g = 0)
    (hdiv : G.divisor f = G.divisor g)
    (hf1 : f.coeff 0 = 1) (hg1 : g.coeff 0 = 1) : f = g := by
  obtain ⟨r, rfl⟩ := hf
  obtain ⟨s, rfl⟩ := hg
  have hr : r ≠ 0 := by
    intro h; simp [h] at hf1
  have hs : s ≠ 0 := by
    intro h; simp [h] at hg1
  rw [G.rationalDivisor r hr hfcusp, G.rationalDivisor s hs hgcusp] at hdiv
  obtain ⟨c, _, hc⟩ := rationalFunction_divisor_rigidity r s hr hs hdiv
  have heq := congrArg rationalHauptmodulExpansion hc
  have hconst : rationalHauptmodulExpansion.comp (algebraMap ℚ (RatFunc ℚ)) =
      HahnSeries.C := Subsingleton.elim _ _
  have hconstc := DFunLike.congr_fun hconst c
  simp only [RingHom.comp_apply] at hconstc
  simp only [map_mul, hconstc] at heq
  have hcoeff := congrArg (fun F : LaurentSeries ℚ => F.coeff 0) heq
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    hf1, hg1, mul_one] at hcoeff
  have hc1 : c = 1 := hcoeff.symm
  simpa [hc1] using heq

/-- E5 gives the full interior divisor and canonical Euler expansion; E6
gives zero cusp orders. Genus-zero descent supplies rationality. The full
divisor rigidity and both leading normalizations are proved internally. -/
theorem actualClassPolynomialLaurentQuotient_eq_canonicalEulerQuotient
    {Form V : Type*} [SMul ℂ Form] [AddCommMonoid V] [Module ℂ V] {n h : ℕ}
    (E : EtaJGeneratorBasis Form)
    {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h}
    (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C)
    (lift : FourComponentInput Form → LaurentSeries ℚ)
    (G : I12MeromorphicGeometry)
    (weylVector : FourComponentInput Form → ℕ → ℂ)
    (hE5 : E5BruinierOno (actualI12BorcherdsModel E C lift G.divisor weylVector))
    (F : FourComponentInput Form) (hn : 0 < n) (hF : VectorInputSpec E n F)
    (pairing : FourComponentInput Form → V →ₗ[ℂ] ℂ)
    (theta : Fin 12 → V) (eta : V) (normalization : ℂ → ℂ)
    (hE6 : E6BruinierSchwagenscheidt
      (componentWeylVectorModel (VectorInputSpec E n) weylVector pairing theta normalization))
    (heta : EtaComponentThetaIdentity theta eta) (hpairing : pairing F eta = 0)
    (hnormalization : normalization 0 = 0)
    (hDescent : I12GenusZeroDescentPrinciple G)
    (hClassCusp : I12ClassPolynomialCuspPrinciple G)
    (hWeylCusp : I12WeylCuspPrinciple G lift weylVector) :
    actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent =
      actualBorcherdsEulerQuotient F := by
  have hweyl := componentWeylVectors_eq_zero (VectorInputSpec E n) weylVector
    pairing theta eta normalization hE6 heta F hF hpairing hnormalization
  have hliftCusp := hWeylCusp F hweyl
  have hliftEuler : lift F = actualBorcherdsEulerQuotient F := (hE5 F ⟨hF, hweyl⟩).2.2
  have hliftLeading : (lift F).coeff 0 = 1 := by
    rw [hliftEuler, actualBorcherdsEulerQuotient_coeff_zero]
  have hlift0 : lift F ≠ 0 := by
    intro hzero; simp [hzero] at hliftLeading
  have hLiftRational := hDescent (lift F) (hE5 F ⟨hF, hweyl⟩).2.1 hliftCusp hlift0
  have hdiv := (actualI12Lift_divisor_eq_full E C lift G weylVector hE5 F hn hF hweyl).trans
    (classPolynomialQuotient_divisor D G hClassCusp).symm
  have heq := eq_of_rational_divisors_and_normalization G (lift F)
    (actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent)
    hLiftRational (classPolynomialQuotient_is_rational D) hliftCusp (hClassCusp D)
    hdiv hliftLeading (actualClassPolynomialLaurentQuotient_leading_normalization D)
  exact heq.symm.trans hliftEuler

end SptCM.Analytic.Repaired
