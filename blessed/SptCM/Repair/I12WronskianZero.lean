module

public import blessed.SptCM.Analytic.Repaired.I12NormalizedProduct
public import blessed.SptCM.Analytic.Repaired.SquareCoefficientVanishing
public import blessed.SptCM.CM.Repaired.I16Reduction
public import blessed.SptCM.Repair.I21ActualLaurentModel

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace SptCM.Repair

open Polynomial
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

noncomputable section

/-- Coefficientwise maps of Hahn series are injective when the coefficient map is. -/
lemma hahnSeries_map_injective {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (fun x : LaurentSeries R => HahnSeries.map x f) := by
  intro x y h
  ext z
  apply hf
  simpa [HahnSeries.map_coeff] using congrArg (fun q : LaurentSeries S => q.coeff z) h

/-- The canonical map from `ℤ[1/6]` to `ℚ` is injective. -/
lemma awaySixToRat_injective :
    Function.Injective SptCM.Analytic.Repaired.awaySixToRat := by
  exact SptCM.CM.Repaired.awaySixToRat_injective

/-- Canonical stabilized Euler products commute with coefficient base change. -/
lemma map_stabilizedEulerProduct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (index exponent : ℕ → ℕ) :
    PowerSeries.map f (stabilizedEulerProduct (R := R) index exponent) =
      stabilizedEulerProduct (R := S) index exponent := by
  ext d
  simp only [PowerSeries.coeff_map, coeff_stabilizedEulerProduct]
  rw [← PowerSeries.coeff_map]
  simp [eulerProductTruncation]

lemma map_eulerProductPlus {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (H : ℤ → ℤ) :
    PowerSeries.map f (eulerProductPlus (R := R) H) =
      eulerProductPlus (R := S) H := by
  exact map_stabilizedEulerProduct f id (positiveEulerExponent H)

lemma map_eulerProductMinus {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (H : ℤ → ℤ) :
    PowerSeries.map f (eulerProductMinus (R := R) H) =
      eulerProductMinus (R := S) H := by
  exact map_stabilizedEulerProduct f id (negativeEulerExponent H)


/-- The integral Hauptmodul and Euler products, base-changed to `ℤ[1/6]`. -/
@[expose]
noncomputable def awayHauptmodulLaurent : LaurentSeries SptCM.AwaySix :=
  HahnSeries.map hauptmodulFormalLaurent (algebraMap ℤ SptCM.AwaySix)

@[expose]
noncomputable def awayEulerPlus (H : ℤ → ℤ) : LaurentSeries SptCM.AwaySix :=
  ((PowerSeries.map (algebraMap ℤ SptCM.AwaySix)
    (eulerProductPlus (R := ℤ) H)) : PowerSeries SptCM.AwaySix)

@[expose]
noncomputable def awayEulerMinus (H : ℤ → ℤ) : LaurentSeries SptCM.AwaySix :=
  ((PowerSeries.map (algebraMap ℤ SptCM.AwaySix)
    (eulerProductMinus (R := ℤ) H)) : PowerSeries SptCM.AwaySix)

lemma map_awayHauptmodul_to_rat :
    HahnSeries.map awayHauptmodulLaurent
      SptCM.Analytic.Repaired.awaySixToRat =
      SptCM.Analytic.Repaired.actualRationalHauptmodulLaurent := by
  ext z
  simp [awayHauptmodulLaurent,
    SptCM.Analytic.Repaired.actualRationalHauptmodulLaurent,
    HahnSeries.map_coeff, SptCM.Analytic.Repaired.awaySixToRat]

lemma map_awayEulerPlus_to_rat (H : ℤ → ℤ) :
    HahnSeries.map (awayEulerPlus H)
      SptCM.Analytic.Repaired.awaySixToRat =
      ((eulerProductPlus (R := ℚ) H : PowerSeries ℚ) : LaurentSeries ℚ) := by
  ext z
  unfold awayEulerPlus
  rw [HahnSeries.map_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hz
  · simp
  · rw [← PowerSeries.coeff_map]
    congr 1
    change ((PowerSeries.map SptCM.Analytic.Repaired.awaySixToRat).comp
      (PowerSeries.map (algebraMap ℤ SptCM.AwaySix)))
        (eulerProductPlus (R := ℤ) H) = _
    rw [← PowerSeries.map_comp]
    apply map_eulerProductPlus

lemma map_awayEulerMinus_to_rat (H : ℤ → ℤ) :
    HahnSeries.map (awayEulerMinus H)
      SptCM.Analytic.Repaired.awaySixToRat =
      ((eulerProductMinus (R := ℚ) H : PowerSeries ℚ) : LaurentSeries ℚ) := by
  ext z
  unfold awayEulerMinus
  rw [HahnSeries.map_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hz
  · simp
  · rw [← PowerSeries.coeff_map]
    congr 1
    change ((PowerSeries.map SptCM.Analytic.Repaired.awaySixToRat).comp
      (PowerSeries.map (algebraMap ℤ SptCM.AwaySix)))
        (eulerProductMinus (R := ℤ) H) = _
    rw [← PowerSeries.map_comp]
    apply map_eulerProductMinus


@[expose]
noncomputable def hahnSeriesMapRingHom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := HahnSeries.map x f
  map_zero' := by
    change HahnSeries.map (0 : LaurentSeries R) f.toZeroHom = 0
    exact HahnSeries.map_zero f.toZeroHom
  map_one' := by
    change HahnSeries.map (1 : LaurentSeries R) f.toMonoidWithZeroHom = 1
    exact HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' x y := by
    change HahnSeries.map (x + y) f.toAddMonoidHom =
      HahnSeries.map x f.toAddMonoidHom + HahnSeries.map y f.toAddMonoidHom
    exact HahnSeries.map_add f.toAddMonoidHom
  map_mul' x y := by
    change HahnSeries.map (x * y) f.toNonUnitalRingHom =
      HahnSeries.map x f.toNonUnitalRingHom * HahnSeries.map y f.toNonUnitalRingHom
    exact HahnSeries.map_mul f.toNonUnitalRingHom

lemma hahnSeriesMapRingHom_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (hahnSeriesMapRingHom f).comp (algebraMap R (LaurentSeries R)) =
      (algebraMap S (LaurentSeries S)).comp f := by
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, hahnSeriesMapRingHom]
  rw [HahnSeries.algebraMap_apply' ℤ a, PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]
  rw [HahnSeries.algebraMap_apply' ℤ (f a), PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]
  simpa using (HahnSeries.map_C (Γ := ℤ) a f)

lemma hahnSeries_map_aeval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : LaurentSeries R) (p : Polynomial R) :
    HahnSeries.map (Polynomial.aeval t p) f =
      Polynomial.aeval (HahnSeries.map t f) (p.map f) := by
  change hahnSeriesMapRingHom f (Polynomial.aeval t p) =
    Polynomial.aeval (hahnSeriesMapRingHom f t) (p.map f)
  exact Polynomial.map_aeval_eq_aeval_map
    (hahnSeriesMapRingHom_algebraMap f).symm p t


end
end SptCM.Repair

namespace SptCM.Repair

lemma laurentSeries_derivative_coe_powerSeries
    {R : Type*} [CommRing R] (p : PowerSeries R) :
    LaurentSeries.derivative R (p : LaurentSeries R) =
      ((PowerSeries.derivative (R := R) p : PowerSeries R) : LaurentSeries R) := by
  ext z
  cases z with
  | ofNat n =>
      have hnat : ((n : ℤ) + 1).natAbs = n + 1 := by omega
      simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv,
        PowerSeries.coeff_derivative, PowerSeries.coeff_coe,
        show ¬(n : ℤ) < 0 by omega,
        show ¬(n : ℤ) + 1 < 0 by omega]
      rw [hnat]
      ring
  | negSucc n =>
      cases n with
      | zero =>
          simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv,
            PowerSeries.coeff_coe]
      | succ n =>
          simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv,
            PowerSeries.coeff_coe,
            show Int.negSucc (n + 1) < 0 by omega,
            show Int.negSucc (n + 1) + 1 < 0 by omega]

end SptCM.Repair

namespace SptCM.Repair

open Polynomial
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

noncomputable section

lemma map_awayHauptmodul_to_zmod (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ)) :
    HahnSeries.map awayHauptmodulLaurent (SptCM.awaySixReduction ℓ h6) =
      actualHauptmodulLaurent ℓ := by
  ext z
  simp [awayHauptmodulLaurent, actualHauptmodulLaurent,
    HahnSeries.map_coeff, SptCM.awaySixReduction]

lemma map_awayEulerPlus_to_zmod (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    (H : ℤ → ℤ) :
    HahnSeries.map (awayEulerPlus H) (SptCM.awaySixReduction ℓ h6) =
      ((eulerProductPlus (R := ZMod ℓ) H : PowerSeries (ZMod ℓ)) :
        LaurentSeries (ZMod ℓ)) := by
  ext z
  unfold awayEulerPlus
  rw [HahnSeries.map_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hz
  · simp
  · rw [← PowerSeries.coeff_map]
    congr 1
    change ((PowerSeries.map (SptCM.awaySixReduction ℓ h6)).comp
      (PowerSeries.map (algebraMap ℤ SptCM.AwaySix)))
        (eulerProductPlus (R := ℤ) H) = _
    rw [← PowerSeries.map_comp]
    apply map_eulerProductPlus

lemma map_awayEulerMinus_to_zmod (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ))
    (H : ℤ → ℤ) :
    HahnSeries.map (awayEulerMinus H) (SptCM.awaySixReduction ℓ h6) =
      ((eulerProductMinus (R := ZMod ℓ) H : PowerSeries (ZMod ℓ)) :
        LaurentSeries (ZMod ℓ)) := by
  ext z
  unfold awayEulerMinus
  rw [HahnSeries.map_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hz
  · simp
  · rw [← PowerSeries.coeff_map]
    congr 1
    change ((PowerSeries.map (SptCM.awaySixReduction ℓ h6)).comp
      (PowerSeries.map (algebraMap ℤ SptCM.AwaySix)))
        (eulerProductMinus (R := ℤ) H) = _
    rw [← PowerSeries.map_comp]
    apply map_eulerProductMinus

end
end SptCM.Repair

namespace SptCM.Repair

open Polynomial
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

noncomputable section

/-- The characteristic-zero normalized quotient identity descends to the
cross-multiplied identity over `ℤ[1/6]` and then reduces coefficientwise. -/
theorem actualClassPolynomial_crossProduct_mod
    {Form : Type*} {n h ℓ : ℕ}
    {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C) (F : FourComponentInput Form)
    (h6 : IsUnit (6 : ZMod ℓ))
    (hquotient :
      actualClassPolynomialLaurentQuotient D
          actualRationalHauptmodulLaurent =
        actualBorcherdsEulerQuotient F) :
    aeval (actualHauptmodulLaurent ℓ)
          (D.A.map (SptCM.awaySixReduction ℓ h6)) *
        ((eulerProductMinus (R := ZMod ℓ) F.scalarSeries :
          PowerSeries (ZMod ℓ)) : LaurentSeries (ZMod ℓ)) =
      ((eulerProductPlus (R := ZMod ℓ) F.scalarSeries :
          PowerSeries (ZMod ℓ)) : LaurentSeries (ZMod ℓ)) *
        aeval (actualHauptmodulLaurent ℓ)
          (D.B.map (SptCM.awaySixReduction ℓ h6)) := by
  have httrans : Transcendental ℚ actualRationalHauptmodulLaurent := by
    exact laurentSeries_transcendental_of_simple_pole
      actualRationalHauptmodulLaurent
      actualRationalHauptmodulLaurent_principalPart.1
      actualRationalHauptmodulLaurent_principalPart.2.2
  have hBpoly : D.B.map SptCM.Analytic.Repaired.awaySixToRat ≠ 0 :=
    (D.monicB.map SptCM.Analytic.Repaired.awaySixToRat).ne_zero
  have hB :
      aeval actualRationalHauptmodulLaurent (D.B.map SptCM.Analytic.Repaired.awaySixToRat) ≠ 0 := by
    intro hz
    apply hBpoly
    apply (transcendental_iff_injective.mp httrans)
    simpa using hz
  have hden :
      (((eulerProductMinus (R := ℚ) F.scalarSeries : PowerSeries ℚ) :
          LaurentSeries ℚ)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun q : LaurentSeries ℚ => q.coeff 0) hz
    have hs := (eulerProducts_spec (R := ℚ) F.scalarSeries).2.2.2.1
    simpa [PowerSeries.coeff_coe, hs] using hc
  have hcrossRat :
      aeval actualRationalHauptmodulLaurent (D.A.map SptCM.Analytic.Repaired.awaySixToRat) *
          ((eulerProductMinus (R := ℚ) F.scalarSeries : PowerSeries ℚ) :
            LaurentSeries ℚ) =
        ((eulerProductPlus (R := ℚ) F.scalarSeries : PowerSeries ℚ) :
            LaurentSeries ℚ) *
          aeval actualRationalHauptmodulLaurent (D.B.map SptCM.Analytic.Repaired.awaySixToRat) := by
    exact (div_eq_div_iff hB hden).mp hquotient
  have hcrossAway :
      aeval awayHauptmodulLaurent D.A * awayEulerMinus F.scalarSeries =
        awayEulerPlus F.scalarSeries * aeval awayHauptmodulLaurent D.B := by
    apply hahnSeries_map_injective SptCM.Analytic.Repaired.awaySixToRat SptCM.Repair.awaySixToRat_injective
    change hahnSeriesMapRingHom SptCM.Analytic.Repaired.awaySixToRat
        (aeval awayHauptmodulLaurent D.A * awayEulerMinus F.scalarSeries) =
      hahnSeriesMapRingHom SptCM.Analytic.Repaired.awaySixToRat
        (awayEulerPlus F.scalarSeries * aeval awayHauptmodulLaurent D.B)
    rw [map_mul, map_mul]
    simpa [hahnSeriesMapRingHom, hahnSeries_map_aeval,
      map_awayHauptmodul_to_rat, map_awayEulerPlus_to_rat,
      map_awayEulerMinus_to_rat] using hcrossRat
  have hz := congrArg
    (fun q : LaurentSeries SptCM.AwaySix =>
      HahnSeries.map q (SptCM.awaySixReduction ℓ h6)) hcrossAway
  change hahnSeriesMapRingHom (SptCM.awaySixReduction ℓ h6)
      (aeval awayHauptmodulLaurent D.A * awayEulerMinus F.scalarSeries) =
    hahnSeriesMapRingHom (SptCM.awaySixReduction ℓ h6)
      (awayEulerPlus F.scalarSeries * aeval awayHauptmodulLaurent D.B) at hz
  rw [map_mul, map_mul] at hz
  simpa [hahnSeriesMapRingHom, hahnSeries_map_aeval,
    map_awayHauptmodul_to_zmod, map_awayEulerPlus_to_zmod,
    map_awayEulerMinus_to_zmod] using hz

end
end SptCM.Repair


namespace SptCM.Repair

open Polynomial
open SptCM.Analytic
open SptCM.Analytic.Repaired
open SptCM.CM.Repaired

noncomputable section


/-- Product rule for a Laurent monomial times an embedded power series. -/
lemma laurentSeries_derivative_single_mul_coe {R : Type*} [CommRing R]
    (a : ℤ) (p : PowerSeries R) :
    LaurentSeries.derivative R
        (HahnSeries.single a 1 * (p : LaurentSeries R)) =
      HahnSeries.single (a - 1) (a : R) * (p : LaurentSeries R) +
        HahnSeries.single a 1 *
          ((PowerSeries.derivative (R := R) p : PowerSeries R) : LaurentSeries R) := by
  ext z
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv,
    HahnSeries.coeff_single_mul, PowerSeries.coeff_coe,
    PowerSeries.coeff_derivative]
  by_cases hlt : z + 1 < a
  · have hlt' : z < a - 1 := by omega
    have hlt'' : z < a := by omega
    simp [hlt, hlt', hlt'']
  · by_cases hza : z < a
    · have hz : z + 1 = a := by omega
      have hnot : ¬ z < a - 1 := by omega
      subst a
      norm_num
    · have hnonneg : 0 ≤ z - a := by omega
      have hindex : z + 1 - a = z - (a - 1) := by omega
      rw [if_neg hlt, if_neg (by omega : ¬z < a - 1), if_neg hza,
        hindex]
      have hi : (z - (a - 1)).natAbs = (z - a).natAbs + 1 := by
        omega
      rw [hi, abs_of_nonneg hnonneg]
      push_cast
      ring

/-- Formal Laurent differentiation obeys the Leibniz rule. -/
lemma laurentSeries_derivative_mul {R : Type*} [CommRing R]
    (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by
  rw [← f.single_order_mul_powerSeriesPart,
    ← g.single_order_mul_powerSeriesPart]
  have hprod :
      (HahnSeries.single f.order 1 *
          (f.powerSeriesPart : LaurentSeries R)) *
        (HahnSeries.single g.order 1 *
          (g.powerSeriesPart : LaurentSeries R)) =
      HahnSeries.single (f.order + g.order) 1 *
        ((f.powerSeriesPart * g.powerSeriesPart : PowerSeries R) :
          LaurentSeries R) := by
    calc
      _ = (HahnSeries.single f.order 1 * HahnSeries.single g.order 1) *
          ((f.powerSeriesPart : LaurentSeries R) *
            (g.powerSeriesPart : LaurentSeries R)) := by ring
      _ = _ := by
        rw [HahnSeries.single_mul_single, PowerSeries.coe_mul]
        simp
  rw [hprod, laurentSeries_derivative_single_mul_coe,
    laurentSeries_derivative_single_mul_coe,
    laurentSeries_derivative_single_mul_coe]
  rw [(PowerSeries.derivative (R := R)).leibniz]
  simp only [map_add, map_mul]
  have hmono :
      HahnSeries.single (f.order + g.order - 1)
          ((f.order + g.order : ℤ) : R) =
        HahnSeries.single (f.order - 1) (f.order : R) *
            HahnSeries.single g.order 1 +
          HahnSeries.single f.order 1 *
            HahnSeries.single (g.order - 1) (g.order : R) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    rw [show (f.order - 1) + g.order = f.order + g.order - 1 by omega,
      show f.order + (g.order - 1) = f.order + g.order - 1 by omega]
    rw [← HahnSeries.single_add]
    push_cast
    congr 1
    ring
  have hs : HahnSeries.single (f.order + g.order) (1 : R) =
      HahnSeries.single f.order 1 * HahnSeries.single g.order 1 := by
    rw [HahnSeries.single_mul_single]
    simp
  rw [hmono, hs]
  simp only [smul_eq_mul]
  simp_rw [PowerSeries.coe_mul]
  ring

/-- The Laurent derivative of a constant series is zero. -/
lemma laurentSeries_derivative_algebraMap {R : Type*} [CommRing R] (a : R) :
    LaurentSeries.derivative R
      (algebraMap R (LaurentSeries R) a) = 0 := by
  rw [HahnSeries.algebraMap_apply' ℤ a, PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]
  ext z
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv]
  rw [HahnSeries.coeff_single]
  split_ifs with hz
  · have hcast : (z : R) + 1 = 0 := by
      have hc := congrArg (fun x : ℤ => (x : R)) hz
      push_cast at hc
      exact hc
    rw [hcast, zero_mul]
  · rw [mul_zero]

/-- Power rule for formal Laurent differentiation. -/
lemma laurentSeries_derivative_pow {R : Type*} [CommRing R]
    (t : LaurentSeries R) (n : ℕ) :
    LaurentSeries.derivative R (t ^ n) =
      n • (t ^ (n - 1) * LaurentSeries.derivative R t) := by
  induction n with
  | zero => simpa using laurentSeries_derivative_algebraMap (R := R) 1
  | succ n ih =>
      rw [pow_succ, laurentSeries_derivative_mul, ih]
      simp only [nsmul_eq_mul, Nat.cast_succ]
      cases n with
      | zero => simp
      | succ n =>
          simp only [Nat.succ_sub_one, pow_succ]
          ring

/-- Chain rule for polynomial evaluation in a Laurent series. -/
lemma laurentSeries_derivative_aeval {R : Type*} [CommRing R]
    (t : LaurentSeries R) (p : Polynomial R) :
    LaurentSeries.derivative R (Polynomial.aeval t p) =
      Polynomial.aeval t p.derivative * LaurentSeries.derivative R t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Polynomial.derivative_add, map_add, hp, hq]
      simp only [map_add]
      ring
  | monomial n a =>
      rw [Polynomial.aeval_monomial, laurentSeries_derivative_mul,
        laurentSeries_derivative_algebraMap, zero_mul, zero_add,
        laurentSeries_derivative_pow, Polynomial.derivative_monomial,
        Polynomial.aeval_monomial]
      simp only [nsmul_eq_mul, map_mul, map_natCast]
      cases n with
      | zero => simp
      | succ n =>
          simp only [Nat.succ_sub_one]
          ring

/-- For the genuine descended class polynomials, canonicality and an
admissible discriminant force the reduced Wronskian to vanish.  The only
analytic input beyond the published grid and theta-cycle interfaces is the
already normalized characteristic-zero Borcherds product identity; reduction,
Euler-exponent divisibility, Frobenius differentiation, and the Laurent-series
chain rule are all performed internally. -/
theorem actualClassPolynomials_wronskian_eq_zero
    {Form Product : Type*} [SMul ℂ Form]
    {n h ℓ : ℕ}
    {C : ActualOrientedCMCoordinates n h}
    (D : ActualClassPolynomialSpec C)
    (E : EtaJGeneratorBasis Form)
    (G : IntegralGridRealization)
    (R : WeightTwoMultiplicationTheory ℚ Form Product E G.rationalGrid)
    [Fact ℓ.Prime]
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hadm : SptCM.Admissible ℓ n)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hquotient :
      actualClassPolynomialLaurentQuotient D
          actualRationalHauptmodulLaurent =
        actualBorcherdsEulerQuotient
          (auxiliaryFourComponentInput E ((n + 1) / 24)
            (aCoeff (n : ℤ)))) :
    SptCM.wronskianObstruction
      (D.actualReducedClassPolynomials ℓ
        (SptCM.six_isUnit_zmod_of_prime_five_le
          hcanonical.prime hcanonical.five_le)).1
      (D.actualReducedClassPolynomials ℓ
        (SptCM.six_isUnit_zmod_of_prime_five_le
          hcanonical.prime hcanonical.five_le)).2 = 0 := by
  let F : FourComponentInput Form :=
    auxiliaryFourComponentInput E ((n + 1) / 24) (aCoeff (n : ℤ))
  let h6 : IsUnit (6 : ZMod ℓ) :=
    SptCM.six_isUnit_zmod_of_prime_five_le
      hcanonical.prime hcanonical.five_le
  have hrange : AnalyticAdmissible ℓ n :=
    ⟨hcanonical.prime, hcanonical.five_le, hadm⟩
  have hEuler : EulerInertMismatchInput ℓ :=
    eulerInertMismatch_of_five_le ℓ hcanonical.five_le
  have hdiv : ∀ m : ℕ,
      ℓ ∣ m ∨
        (ℓ ∣ positiveEulerExponent F.scalarSeries m ∧
          ℓ ∣ negativeEulerExponent F.scalarSeries m) := by
    intro m
    by_cases hmℓ : ℓ ∣ m
    · exact Or.inl hmℓ
    · right
      have hsigned :
          (signedEulerExponent F.scalarSeries m : ZMod ℓ) = 0 := by
        by_cases hm6 : Nat.Coprime m 6
        · have hmAllowed : ValidGridIndex ℓ m := by
            exact hm6.mul_right
              ((hcanonical.prime.coprime_iff_not_dvd).2 hmℓ).symm
          have hsq :=
            actual_square_coefficient_vanish G E R ℓ n m
              hcanonical hadm hmAllowed hAK hEuler
          have hH :
              (F.scalarSeries ((m : ℤ) ^ 2) : ZMod ℓ) = 0 := by
            simpa only [F, auxiliaryFourComponentInput, actualAuxiliarySeries] using hsq
          simp [signedEulerExponent, hH]
        · rw [show signedEulerExponent F.scalarSeries m = 0 from
            signedEulerExponent_eq_zero_of_not_coprime_six F.scalarSeries hm6]
          exact Int.cast_zero
      have hdiff :
          (positiveEulerExponent F.scalarSeries m : ZMod ℓ) -
              (negativeEulerExponent F.scalarSeries m : ZMod ℓ) = 0 := by
        rw [positive_sub_negativeEulerExponent_zmod]
        exact hsigned
      rcases positive_or_negativeEulerExponent_eq_zero F.scalarSeries m with hp | hn
      · rw [hp] at hdiff ⊢
        constructor
        · exact dvd_zero ℓ
        · have hz : (negativeEulerExponent F.scalarSeries m : ZMod ℓ) = 0 := by
            simpa using hdiff
          exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ
            (negativeEulerExponent F.scalarSeries m)).mp hz
      · rw [hn] at hdiff ⊢
        constructor
        · have hz : (positiveEulerExponent F.scalarSeries m : ZMod ℓ) = 0 := by
            simpa using hdiff
          exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ
            (positiveEulerExponent F.scalarSeries m)).mp hz
        · exact dvd_zero ℓ
  have hspec := eulerProducts_spec (R := ZMod ℓ) F.scalarSeries
  have hnumeratorPS :
      PowerSeries.derivative (R := ZMod ℓ)
          (eulerProductPlus F.scalarSeries : PowerSeries (ZMod ℓ)) = 0 :=
    SptCM.stabilizedEulerProduct_derivative_eq_zero ℓ
      (eulerProductPlus F.scalarSeries) id
      (positiveEulerExponent F.scalarSeries) hspec.1
      (fun m => (hdiv m).imp_right And.left)
  have hdenominatorPS :
      PowerSeries.derivative (R := ZMod ℓ)
          (eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) = 0 :=
    SptCM.stabilizedEulerProduct_derivative_eq_zero ℓ
      (eulerProductMinus F.scalarSeries) id
      (negativeEulerExponent F.scalarSeries) hspec.2.1
      (fun m => (hdiv m).imp_right And.right)
  have hnumerator :
      LaurentSeries.derivative (ZMod ℓ)
          ((eulerProductPlus F.scalarSeries : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)) = 0 := by
    rw [laurentSeries_derivative_coe_powerSeries, hnumeratorPS]
    simp
  have hdenominatorDeriv :
      LaurentSeries.derivative (ZMod ℓ)
          ((eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)) = 0 := by
    rw [laurentSeries_derivative_coe_powerSeries, hdenominatorPS]
    simp
  have hdenominator :
      (((eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) :
        LaurentSeries (ZMod ℓ))) ≠ 0 := by
    intro hz
    have hc := congrArg
      (fun q : LaurentSeries (ZMod ℓ) => q.coeff 0) hz
    simpa [PowerSeries.coeff_coe, hspec.2.2.2.1] using hc
  have hproduct := actualClassPolynomial_crossProduct_mod D F h6
    (by simpa [F] using hquotient)
  have httrans : Transcendental (ZMod ℓ) (actualHauptmodulLaurent ℓ) := by
    simpa [actualLaurentHauptmodulData_series] using
      (actualLaurentHauptmodulData ℓ n hrange).transcendental
  have htderiv :
      LaurentSeries.derivative (ZMod ℓ) (actualHauptmodulLaurent ℓ) ≠ 0 := by
    simpa [actualLaurentHauptmodulData_series] using
      (actualLaurentHauptmodulData ℓ n hrange).derivative_ne_zero
  change SptCM.wronskianObstruction
      (D.A.map (SptCM.awaySixReduction ℓ h6))
      (D.B.map (SptCM.awaySixReduction ℓ h6)) = 0
  have hderiv := congrArg (LaurentSeries.derivative (ZMod ℓ)) hproduct
  rw [laurentSeries_derivative_mul, laurentSeries_derivative_mul,
    hnumerator, hdenominatorDeriv] at hderiv
  have hderiv' :
      LaurentSeries.derivative (ZMod ℓ)
          (aeval (actualHauptmodulLaurent ℓ)
            (D.A.map (SptCM.awaySixReduction ℓ h6))) *
          ((eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)) =
        ((eulerProductPlus F.scalarSeries : PowerSeries (ZMod ℓ)) :
            LaurentSeries (ZMod ℓ)) *
          LaurentSeries.derivative (ZMod ℓ)
            (aeval (actualHauptmodulLaurent ℓ)
              (D.B.map (SptCM.awaySixReduction ℓ h6))) := by
    simpa [mul_comm] using hderiv
  have hcross :
      LaurentSeries.derivative (ZMod ℓ)
          (aeval (actualHauptmodulLaurent ℓ)
            (D.A.map (SptCM.awaySixReduction ℓ h6))) *
          aeval (actualHauptmodulLaurent ℓ)
            (D.B.map (SptCM.awaySixReduction ℓ h6)) -
        aeval (actualHauptmodulLaurent ℓ)
            (D.A.map (SptCM.awaySixReduction ℓ h6)) *
          LaurentSeries.derivative (ZMod ℓ)
            (aeval (actualHauptmodulLaurent ℓ)
              (D.B.map (SptCM.awaySixReduction ℓ h6))) = 0 := by
    apply mul_right_cancel₀ hdenominator
    rw [zero_mul]
    calc
      _ = (LaurentSeries.derivative (ZMod ℓ)
              (aeval (actualHauptmodulLaurent ℓ)
                (D.A.map (SptCM.awaySixReduction ℓ h6))) *
            ((eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) :
              LaurentSeries (ZMod ℓ))) *
            aeval (actualHauptmodulLaurent ℓ)
              (D.B.map (SptCM.awaySixReduction ℓ h6)) -
          LaurentSeries.derivative (ZMod ℓ)
              (aeval (actualHauptmodulLaurent ℓ)
                (D.B.map (SptCM.awaySixReduction ℓ h6))) *
            (aeval (actualHauptmodulLaurent ℓ)
                (D.A.map (SptCM.awaySixReduction ℓ h6)) *
              ((eulerProductMinus F.scalarSeries : PowerSeries (ZMod ℓ)) :
                LaurentSeries (ZMod ℓ))) := by ring
      _ = (((eulerProductPlus F.scalarSeries : PowerSeries (ZMod ℓ)) :
              LaurentSeries (ZMod ℓ)) *
            LaurentSeries.derivative (ZMod ℓ)
              (aeval (actualHauptmodulLaurent ℓ)
                (D.B.map (SptCM.awaySixReduction ℓ h6)))) *
            aeval (actualHauptmodulLaurent ℓ)
              (D.B.map (SptCM.awaySixReduction ℓ h6)) -
          LaurentSeries.derivative (ZMod ℓ)
              (aeval (actualHauptmodulLaurent ℓ)
                (D.B.map (SptCM.awaySixReduction ℓ h6))) *
            (((eulerProductPlus F.scalarSeries : PowerSeries (ZMod ℓ)) :
                LaurentSeries (ZMod ℓ)) *
              aeval (actualHauptmodulLaurent ℓ)
                (D.B.map (SptCM.awaySixReduction ℓ h6))) := by
            rw [hderiv', hproduct]
      _ = 0 := by ring
  rw [laurentSeries_derivative_aeval,
    laurentSeries_derivative_aeval] at hcross
  have hchain :
      aeval (actualHauptmodulLaurent ℓ)
          (SptCM.wronskianObstruction
            (D.A.map (SptCM.awaySixReduction ℓ h6))
            (D.B.map (SptCM.awaySixReduction ℓ h6))) *
        LaurentSeries.derivative (ZMod ℓ) (actualHauptmodulLaurent ℓ) = 0 := by
    rw [SptCM.wronskianObstruction, Polynomial.derivative_map,
      Polynomial.derivative_map, map_sub, map_mul, map_mul]
    calc
      _ = ((aeval (actualHauptmodulLaurent ℓ)
              ((D.A.derivative).map (SptCM.awaySixReduction ℓ h6)) *
            LaurentSeries.derivative (ZMod ℓ) (actualHauptmodulLaurent ℓ)) *
            aeval (actualHauptmodulLaurent ℓ)
              (D.B.map (SptCM.awaySixReduction ℓ h6)) -
          aeval (actualHauptmodulLaurent ℓ)
              (D.A.map (SptCM.awaySixReduction ℓ h6)) *
            (aeval (actualHauptmodulLaurent ℓ)
                ((D.B.derivative).map (SptCM.awaySixReduction ℓ h6)) *
              LaurentSeries.derivative (ZMod ℓ)
                (actualHauptmodulLaurent ℓ)) ) := by ring
      _ = 0 := by simpa [Polynomial.derivative_map] using hcross
  have heval :
      aeval (actualHauptmodulLaurent ℓ)
          (SptCM.wronskianObstruction
            (D.A.map (SptCM.awaySixReduction ℓ h6))
            (D.B.map (SptCM.awaySixReduction ℓ h6))) = 0 :=
    (mul_eq_zero.mp hchain).resolve_right htderiv
  exact (transcendental_iff_injective.mp httrans) (by simpa using heval)


end

end SptCM.Repair
