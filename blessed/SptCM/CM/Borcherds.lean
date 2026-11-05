module

public import blessed.SptCM.CM.ClassPolynomials
public import blessed.SptCM.Analytic.DualityPairing
public import blessed.SptCM.Analytic.ProductObstruction
public import blessed.SptCM.PaperInterfaces
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.LaurentSeries

public section

-- Keep the existing ring operations on ZMod; the generic group reconstruction
-- introduced in this Mathlib version creates an incompatible negation instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Algebraic deductions from the Borcherds product

Bruinier--Ono's divisor theorem, the Weyl-vector formula, and the analytic
rigidity of a divisor-zero modular function are cited external inputs in the
paper.  They occur below as explicit hypotheses.  The normalization and
characteristic-`ℓ` deductions are proved here.
-/

namespace SptCM

open Polynomial
open PaperInterfaces

/-- If divisor rigidity says two meromorphic modular functions differ by a
constant, and the leading-value functional is multiplicative by constants
and sends both functions to one, then the normalized functions agree. -/
theorem classPoly_product_of_divisor_rigidity
    {K F : Type*} [Field K] [CommRing F] [Algebra K F]
    (leadingValue : F → K) (classQuotient borcherdsProduct : F)
    (hrigidity : ∃ c : K, borcherdsProduct = algebraMap K F c * classQuotient)
    (hleading_smul : ∀ (c : K) (f : F),
      leadingValue (algebraMap K F c * f) = c * leadingValue f)
    (hclass_normalized : leadingValue classQuotient = 1)
    (hborcherds_normalized : leadingValue borcherdsProduct = 1) :
    classQuotient = borcherdsProduct := by
  rcases hrigidity with ⟨c, hc⟩
  have hcone : c = 1 := by
    have h := congrArg leadingValue hc
    rw [hleading_smul, hclass_normalized, hborcherds_normalized, mul_one] at h
    exact h.symm
  subst c
  simpa using hc.symm

/-- Paper-facing form of the normalized Borcherds-product argument.  The two
literature inputs are used only for their stated conclusions: the Weyl formula
turns the already-computed regularized pairings into zero cusp exponents, and
the Borcherds theorem supplies the divisor, character, and product expansion.
The remaining `hrigidity` hypothesis is the standard divisor-zero rigidity
principle, stated as an implication from matching divisors and vanishing cusp
exponents rather than as the desired normalized identity. -/
theorem normalized_classPoly_eq_borcherdsProduct
    {Input Divisor Product Theta Scalar Cusp K : Type*}
    [Field K] [CommRing Product] [Algebra K Product] [Zero Scalar]
    (BL : BorcherdsLiftData Input Divisor Product)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput BL)
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor) (classQuotient : Product)
    (leadingValue : Product → K)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : BL.predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      BL.divisor (BL.lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : K, BL.lift F = algebraMap K Product c * classQuotient)
    (hleading_smul : ∀ (c : K) (f : Product),
      leadingValue (algebraMap K Product c * f) = c * leadingValue f)
    (hclass_normalized : leadingValue classQuotient = 1)
    (hlift_normalized : leadingValue (BL.lift F) = 1) :
    classQuotient = BL.lift F ∧
      BL.hasProductExpansion F classQuotient := by
  have hweyl_zero : ∀ c : Cusp, WV.weylVector F c = 0 := by
    intro c
    rw [hWV F c, hpairing c, hnormalization_zero]
  have hcusp : CuspExponentsVanish := hcusp_of_weyl hweyl_zero
  have hlift := hBL F
  have hdivisor : BL.divisor (BL.lift F) = classDivisor := by
    rw [hlift.1, hpredicted_divisor]
  have heq : classQuotient = BL.lift F :=
    classPoly_product_of_divisor_rigidity leadingValue classQuotient
      (BL.lift F) (hrigidity hdivisor hcusp) hleading_smul
      hclass_normalized hlift_normalized
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hlift.2.2

/-- Concrete class-polynomial quotient form of the preceding theorem.  Here
the abstract class quotient is fixed to `A(t)/B(t)`, and the meaning of the
model's product-expansion predicate is fixed to the displayed Euler-product
quotient. -/
theorem normalized_classPolynomial_quotient_product_identity
    {Input Divisor M Theta Scalar Cusp K : Type*}
    [Field K] [Field M] [Algebra K M] [Zero Scalar]
    (BL : BorcherdsLiftData Input Divisor M)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput BL)
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor)
    (t : M) (A B : Polynomial K) (productNumerator productDenominator : M)
    (leadingValue : M → K)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : BL.predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      BL.divisor (BL.lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : K, BL.lift F =
          algebraMap K M c * (aeval t A / aeval t B))
    (hleading_smul : ∀ (c : K) (f : M),
      leadingValue (algebraMap K M c * f) = c * leadingValue f)
    (hclass_normalized : leadingValue (aeval t A / aeval t B) = 1)
    (hlift_normalized : leadingValue (BL.lift F) = 1)
    (hproduct_expansion :
      ∀ g : M, BL.hasProductExpansion F g ↔
        g = productNumerator / productDenominator) :
    aeval t A / aeval t B =
        productNumerator / productDenominator := by
  obtain ⟨_, hexpansion⟩ :=
    normalized_classPoly_eq_borcherdsProduct BL WV hBL hWV F
      classDivisor (aeval t A / aeval t B) leadingValue hpairing
      hnormalization_zero hpredicted_divisor CuspExponentsVanish
      hcusp_of_weyl hrigidity hleading_smul hclass_normalized
      hlift_normalized
  exact (hproduct_expansion _).mp hexpansion

/-- A Borcherds interface whose product-expansion field has the concrete
meaning `g = numerator F / denominator F`.  Using this constructor prevents a
later theorem from postulating a bridge out of an opaque expansion predicate. -/
@[expose]
def quotientBorcherdsLiftData
    {Input Divisor M : Type*} [Field M]
    (lift : Input → M) (divisor : M → Divisor)
    (predictedDivisor : Input → Divisor)
    (hasUnitaryCharacter : M → Prop)
    (numerator denominator : Input → M) :
    BorcherdsLiftData Input Divisor M where
  lift := lift
  divisor := divisor
  predictedDivisor := predictedDivisor
  hasUnitaryCharacter := hasUnitaryCharacter
  hasProductExpansion := fun F g => g = numerator F / denominator F

/-- The actual class-polynomial quotient/product identity for the concrete
quotient Borcherds interface. -/
theorem normalized_classPolynomial_quotient_eq_concrete_product
    {Input Divisor M Theta Scalar Cusp K : Type*}
    [Field K] [Field M] [Algebra K M] [Zero Scalar]
    (lift : Input → M) (divisor : M → Divisor)
    (predictedDivisor : Input → Divisor)
    (hasUnitaryCharacter : M → Prop)
    (productNumerator productDenominator : Input → M)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput
      (quotientBorcherdsLiftData lift divisor predictedDivisor
        hasUnitaryCharacter productNumerator productDenominator))
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor)
    (t : M) (A B : Polynomial K) (leadingValue : M → K)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      divisor (lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : K, lift F =
          algebraMap K M c * (aeval t A / aeval t B))
    (hleading_smul : ∀ (c : K) (f : M),
      leadingValue (algebraMap K M c * f) = c * leadingValue f)
    (hclass_normalized : leadingValue (aeval t A / aeval t B) = 1)
    (hlift_normalized : leadingValue (lift F) = 1) :
    aeval t A / aeval t B =
      productNumerator F / productDenominator F := by
  apply normalized_classPolynomial_quotient_product_identity
    (quotientBorcherdsLiftData lift divisor predictedDivisor
      hasUnitaryCharacter productNumerator productDenominator)
    WV hBL hWV F classDivisor t A B
    (productNumerator F) (productDenominator F) leadingValue hpairing
    hnormalization_zero hpredicted_divisor CuspExponentsVanish
    hcusp_of_weyl hrigidity hleading_smul hclass_normalized
    hlift_normalized
  intro g
  rfl

/-- Coefficientwise definition of an infinite Euler product.  The coefficient
of degree `d` is required to agree with a finite truncation; the slightly
larger range `d+2` is convenient for differentiating, and expresses the usual
stabilization fact that only finitely many Euler factors affect a fixed
coefficient. -/
@[expose]
def IsStabilizedEulerProduct
    {R : Type*} [CommRing R]
    (P : PowerSeries R) (index exponent : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, PowerSeries.coeff d P =
    PowerSeries.coeff d
      (∏ i ∈ Finset.range (d + 2),
        (1 - PowerSeries.X ^ index i) ^ exponent i)

/-- Exact infinite-formal-product specialization of the normalized
Borcherds theorem.  `numerator` and `denominator` are full stabilized power
series; their canonical images in the Laurent-series field form the product
on the right-hand side. -/
theorem normalized_classPolynomial_quotient_eq_infiniteEulerProduct
    {Input Divisor Theta Scalar Cusp K : Type*}
    [Field K] [Zero Scalar]
    (lift : Input → LaurentSeries K)
    (divisor : LaurentSeries K → Divisor)
    (predictedDivisor : Input → Divisor)
    (hasUnitaryCharacter : LaurentSeries K → Prop)
    (numerator denominator : PowerSeries K)
    (index eplus eminus : ℕ → ℕ)
    (hnumeratorProduct :
      IsStabilizedEulerProduct numerator index eplus)
    (hdenominatorProduct :
      IsStabilizedEulerProduct denominator index eminus)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput
      (quotientBorcherdsLiftData lift divisor predictedDivisor
        hasUnitaryCharacter
        (fun _ => (numerator : LaurentSeries K))
        (fun _ => (denominator : LaurentSeries K))))
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor)
    (t : LaurentSeries K) (A B : Polynomial K)
    (leadingValue : LaurentSeries K → K)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      divisor (lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : K, lift F =
          algebraMap K (LaurentSeries K) c * (aeval t A / aeval t B))
    (hleading_smul : ∀ (c : K) (f : LaurentSeries K),
      leadingValue (algebraMap K (LaurentSeries K) c * f) =
        c * leadingValue f)
    (hclass_normalized : leadingValue (aeval t A / aeval t B) = 1)
    (hlift_normalized : leadingValue (lift F) = 1) :
    aeval t A / aeval t B =
        (numerator : LaurentSeries K) / (denominator : LaurentSeries K) ∧
      IsStabilizedEulerProduct numerator index eplus ∧
      IsStabilizedEulerProduct denominator index eminus := by
  refine ⟨?_, hnumeratorProduct, hdenominatorProduct⟩
  exact normalized_classPolynomial_quotient_eq_concrete_product
    lift divisor predictedDivisor hasUnitaryCharacter
    (fun _ => (numerator : LaurentSeries K))
    (fun _ => (denominator : LaurentSeries K))
    WV hBL hWV F classDivisor t A B leadingValue hpairing
    hnormalization_zero hpredicted_divisor CuspExponentsVanish
    hcusp_of_weyl hrigidity hleading_smul hclass_normalized
    hlift_normalized

/-- Equality of quotients after embedding power series into Laurent series
descends to the cross-multiplied identity in power series.  The only
additional hypotheses are precisely that the two denominators are nonzero. -/
theorem powerSeries_crossProduct_of_laurentSeries_quotient
    {K : Type*} [Field K]
    (t numerator denominator : PowerSeries K) (A B : Polynomial K)
    (hB : aeval t B ≠ 0) (hdenominator : denominator ≠ 0)
    (hratio :
      aeval (t : LaurentSeries K) A / aeval (t : LaurentSeries K) B =
        (numerator : LaurentSeries K) / (denominator : LaurentSeries K)) :
    aeval t A * denominator = numerator * aeval t B := by
  have hmap_aeval (P : Polynomial K) :
      ((aeval t P : PowerSeries K) : LaurentSeries K) =
        aeval (t : LaurentSeries K) P := by
    simpa using
      (Polynomial.map_aeval_eq_aeval_map
        (φ := RingHom.id K)
        (ψ := HahnSeries.ofPowerSeries ℤ K)
        (by
          ext x
          simp [LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
            HahnSeries.ofPowerSeries_C]) P t)
  have hB' : aeval (t : LaurentSeries K) B ≠ 0 := by
    intro hzero
    apply hB
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa [hmap_aeval] using hzero
  have hdenominator' : (denominator : LaurentSeries K) ≠ 0 := by
    intro hzero
    apply hdenominator
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  have hcross :
      aeval (t : LaurentSeries K) A * (denominator : LaurentSeries K) =
        (numerator : LaurentSeries K) * aeval (t : LaurentSeries K) B :=
    (div_eq_div_iff hB' hdenominator').mp hratio
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  simpa [hmap_aeval] using hcross

/-- The Frobenius identity used on every Euler factor after reduction modulo
`ℓ`. -/
theorem eulerFactor_frobenius
    {R : Type*} [CommRing R] (ℓ m : ℕ) [Fact ℓ.Prime] [CharP R ℓ]
    (q : R) :
    (1 - q ^ m) ^ ℓ = 1 - q ^ (ℓ * m) := by
  rw [sub_pow_char, one_pow]
  congr 1
  calc
    (q ^ m) ^ ℓ = q ^ (m * ℓ) := (pow_mul q m ℓ).symm
    _ = q ^ (ℓ * m) := by rw [Nat.mul_comm]

/-- The same identity with an exponent known to be a multiple of `ℓ`. -/
theorem eulerFactor_multiple_exponent
    {R : Type*} [CommRing R] (ℓ m e : ℕ) [Fact ℓ.Prime] [CharP R ℓ]
    (q : R) :
    (1 - q ^ m) ^ (ℓ * e) = (1 - q ^ (ℓ * m)) ^ e := by
  rw [pow_mul, eulerFactor_frobenius]

/-- A derivation kills an Euler factor if either its index or its exponent is
a multiple of the characteristic.  This is the factorwise Frobenius
calculation used in the paper. -/
theorem derivation_eulerFactor_eq_zero_of_dvd
    {S : Type*} [CommRing S] (ℓ m e : ℕ) [Fact ℓ.Prime] [CharP S ℓ]
    [Algebra (ZMod ℓ) S]
    (D : Derivation (ZMod ℓ) S S) (q : S)
    (hdiv : ℓ ∣ m ∨ ℓ ∣ e) :
    D ((1 - q ^ m) ^ e) = 0 := by
  rcases hdiv with hm | he
  · rcases hm with ⟨k, rfl⟩
    rw [← eulerFactor_frobenius ℓ k q]
    rw [D.leibniz_pow, Analytic.derivation_pow_char_eq_zero D]
    simp
  · rcases he with ⟨k, rfl⟩
    rw [Nat.mul_comm ℓ k, pow_mul]
    exact Analytic.derivation_pow_char_eq_zero D _

/-- A finite product of Euler factors is killed by the derivation when every
factor satisfies the preceding Frobenius alternative. -/
theorem derivation_finset_eulerProduct_eq_zero
    {ι S : Type*} [DecidableEq ι] [CommRing S]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ] [Algebra (ZMod ℓ) S]
    (D : Derivation (ZMod ℓ) S S) (q : S)
    (s : Finset ι) (index exponent : ι → ℕ)
    (hdiv : ∀ i ∈ s, ℓ ∣ index i ∨ ℓ ∣ exponent i) :
    D (∏ i ∈ s, (1 - q ^ index i) ^ exponent i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, D.leibniz,
        derivation_eulerFactor_eq_zero_of_dvd ℓ (index i) (exponent i) D q
          (hdiv i (Finset.mem_insert_self i s))]
      have hs : D (∏ j ∈ s, (1 - q ^ index j) ^ exponent j) = 0 :=
        ih (fun j hj => hdiv j (Finset.mem_insert_of_mem hj))
      rw [hs]
      simp

/-- An actual stabilized infinite Euler product whose every factor satisfies
the Frobenius alternative has zero derivative.  This upgrades the finite
factor calculation to the full formal series coefficientwise. -/
theorem stabilizedEulerProduct_derivative_eq_zero
    (ℓ : ℕ) [Fact ℓ.Prime]
    (P : PowerSeries (ZMod ℓ)) (index exponent : ℕ → ℕ)
    (hproduct : IsStabilizedEulerProduct P index exponent)
    (hdiv : ∀ i : ℕ, ℓ ∣ index i ∨ ℓ ∣ exponent i) :
    PowerSeries.derivative (R := ZMod ℓ) P = 0 := by
  letI : CharP (PowerSeries (ZMod ℓ)) ℓ :=
    charP_of_injective_ringHom PowerSeries.C_injective ℓ
  ext d
  rw [PowerSeries.coeff_derivative]
  rw [hproduct (d + 1)]
  have hfinite :=
    derivation_finset_eulerProduct_eq_zero ℓ
      (PowerSeries.derivative (R := ZMod ℓ)) PowerSeries.X
      (Finset.range (d + 1 + 2)) index exponent
      (fun i _ => hdiv i)
  have hc := congrArg (PowerSeries.coeff d) hfinite
  rw [PowerSeries.coeff_derivative] at hc
  simpa using hc

/-- The coefficient-duality square-vanishing lemma implies the exact
factorwise divisibility alternative needed for Frobenius.  The two natural
exponents are the positive and negative parts of the signed coefficient, as
recorded by `honeSide`. -/
theorem euler_exponents_dvd_of_Hn_square_vanishing
    (ℓ n m eplus eminus : ℕ) [Fact ℓ.Prime]
    (H : Analytic.HForm (ZMod ℓ)) (a b chi : ZMod ℓ)
    (hnorm : Analytic.HasHnNormalization n a H)
    (hconstant :
      b + H ((m : ℤ) ^ 2) - chi * H 1 = 0)
    (ha : a = 0) (hb : b = 0)
    (hexponent :
      (eplus : ZMod ℓ) - (eminus : ZMod ℓ) = H ((m : ℤ) ^ 2))
    (honeSide : eplus = 0 ∨ eminus = 0) :
    ℓ ∣ m ∨ (ℓ ∣ eplus ∧ ℓ ∣ eminus) := by
  by_cases hm : ℓ ∣ m
  · exact Or.inl hm
  · right
    have hH : H ((m : ℤ) ^ 2) = 0 :=
      Analytic.Hn_square_coefficient_eq_zero hnorm hconstant ha hb
    have hdiff :
        (eplus : ZMod ℓ) - (eminus : ZMod ℓ) = 0 := by
      rw [hexponent, hH]
    rcases honeSide with hp | hn
    · subst eplus
      constructor
      · exact dvd_zero ℓ
      · have hz : (eminus : ZMod ℓ) = 0 := by simpa using hdiff
        exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ eminus).mp hz
    · subst eminus
      constructor
      · have hz : (eplus : ZMod ℓ) = 0 := by simpa using hdiff
        exact (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ eplus).mp hz
      · exact dvd_zero ℓ

/-- Once square-coefficient vanishing has been proved, the Euler exponents
are divisible by the characteristic away from indices divisible by it.  This
is the purely algebraic part of
`euler_exponents_dvd_of_Hn_square_vanishing`: it needs neither a normalization
of `H` nor the auxiliary coefficients used to establish the vanishing. -/
theorem euler_exponents_dvd_of_square_coefficient_eq_zero
    (ℓ m eplus eminus : ℕ) [Fact ℓ.Prime]
    (H : Analytic.HForm (ZMod ℓ))
    (hH : H ((m : ℤ) ^ 2) = 0)
    (hexponent :
      (eplus : ZMod ℓ) - (eminus : ZMod ℓ) = H ((m : ℤ) ^ 2))
    (honeSide : eplus = 0 ∨ eminus = 0) :
    ℓ ∣ m ∨ (ℓ ∣ eplus ∧ ℓ ∣ eminus) := by
  by_cases hm : ℓ ∣ m
  · exact Or.inl hm
  · right
    have hdiff :
        (eplus : ZMod ℓ) - (eminus : ZMod ℓ) = 0 := by
      rw [hexponent, hH]
    rcases honeSide with hp | hn
    · subst eplus
      constructor
      · exact dvd_zero ℓ
      · have hz : (eminus : ZMod ℓ) = 0 := by simpa using hdiff
        exact (ZMod.natCast_eq_zero_iff eminus ℓ).mp hz
    · subst eminus
      constructor
      · have hz : (eplus : ZMod ℓ) = 0 := by simpa using hdiff
        exact (ZMod.natCast_eq_zero_iff eplus ℓ).mp hz
      · exact dvd_zero ℓ

/-- Injective substitution and a nonzero theta factor turn the chain-rule
equation into polynomial Wronskian vanishing. -/
theorem wronskian_zero_of_injective_substitution
    {ℓ : ℕ} {S : Type*} [CommRing S] [IsDomain S]
    (A B : Polynomial (ZMod ℓ))
    (substitution : Polynomial (ZMod ℓ) →+* S)
    (hsubstitution : Function.Injective substitution)
    (thetaT : S) (hthetaT : thetaT ≠ 0)
    (hchain : substitution (wronskianObstruction A B) * thetaT = 0) :
    wronskianObstruction A B = 0 := by
  have hmapped : substitution (wronskianObstruction A B) = 0 :=
    (mul_eq_zero.mp hchain).resolve_right hthetaT
  exact hsubstitution (by simpa using hmapped)

/-- Algebraic core of Proposition `W_n = 0`.  The cited Borcherds product,
coefficient duality, Frobenius support calculation, and chain rule supply
`hchain`; injectivity of Hauptmodul substitution and the nonzero leading term
of `Θ(t)` then force the polynomial Wronskian itself to vanish. -/
theorem canonicalCongruence_forces_wronskian_zero
    {ℓ : ℕ} {S : Type*} [CommRing S] [IsDomain S]
    (A B : Polynomial (ZMod ℓ))
    (substitution : Polynomial (ZMod ℓ) →+* S)
    (hsubstitution : Function.Injective substitution)
    (thetaT : S) (hthetaT : thetaT ≠ 0)
    (hchain : CanonicalCongruencePrime ℓ →
      substitution (wronskianObstruction A B) * thetaT = 0)
    (hcanonical : CanonicalCongruencePrime ℓ) :
    wronskianObstruction A B = 0 := by
  exact wronskian_zero_of_injective_substitution A B substitution
    hsubstitution thetaT hthetaT (hchain hcanonical)


/-- Full algebraic product-to-obstruction bridge.  The analytic input is now
only the concrete quotient identity and the Frobenius derivative vanishings;
the chain rule, cancellation, and transcendental substitution are internal. -/
theorem wronskian_zero_of_borcherds_quotient
    {R S : Type*} [CommRing R] [CommRing S] [NoZeroDivisors S]
    [Algebra R S]
    (D : Derivation R S S) (t : S) (A B : Polynomial R)
    (htrans : Transcendental R t) (ht : D t ≠ 0)
    (numerator denominator : S)
    (hdenominator : denominator ≠ 0)
    (hproduct : aeval t A * denominator = numerator * aeval t B)
    (hnumerator : D numerator = 0)
    (hdenominatorDeriv : D denominator = 0) :
    wronskianObstruction A B = 0 := by
  exact Analytic.wronskianObstruction_eq_zero_of_zero_derivative_quotient
    D t A B htrans ht numerator denominator hdenominator hproduct
      hnumerator hdenominatorDeriv

/-- Paper-facing canonical version of the preceding bridge.  Canonicality is
used only to obtain the two derivative vanishings from the already established
coefficient-support calculation; it is not replaced by a final Wronskian
assumption. -/
theorem canonical_wronskian_zero_of_borcherds_quotient
    {ℓ : ℕ} {S : Type*} [CommRing S] [NoZeroDivisors S]
    [Algebra (ZMod ℓ) S]
    (D : Derivation (ZMod ℓ) S S) (t : S)
    (A B : Polynomial (ZMod ℓ))
    (htrans : Transcendental (ZMod ℓ) t) (ht : D t ≠ 0)
    (numerator denominator : S)
    (hdenominator : denominator ≠ 0)
    (hproduct : aeval t A * denominator = numerator * aeval t B)
    (hFrobenius : CanonicalCongruencePrime ℓ →
      D numerator = 0 ∧ D denominator = 0)
    (hcanonical : CanonicalCongruencePrime ℓ) :
    wronskianObstruction A B = 0 := by
  rcases hFrobenius hcanonical with ⟨hn, hd⟩
  exact wronskian_zero_of_borcherds_quotient D t A B htrans ht
    numerator denominator hdenominator hproduct hn hd

/-- Exact paper-facing product-to-Wronskian deduction.  Unlike
`canonical_wronskian_zero_of_borcherds_quotient`, this theorem obtains the
normalized quotient and its product expansion from the stated
Bruinier--Ono/Weyl interfaces.  The final specialization hypothesis
`hFrobenius_of_expansion` is the coefficient-support calculation: from that
product expansion and the four mathematical hypotheses of the proposition it
produces the two derivative vanishings.  It does not assume a Wronskian or
chain-rule conclusion. -/
theorem canonicalCongruence_forces_wronskian_zero_from_borcherds
    (ℓ n : ℕ) [Fact ℓ.Prime]
    {Input Divisor S Theta Scalar Cusp : Type*}
    [CommRing S] [NoZeroDivisors S] [Algebra (ZMod ℓ) S] [Zero Scalar]
    (BL : BorcherdsLiftData Input Divisor S)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput BL)
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor) (classQuotient : S)
    (leadingValue : S → ZMod ℓ)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : BL.predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      BL.divisor (BL.lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : ZMod ℓ,
          BL.lift F = algebraMap (ZMod ℓ) S c * classQuotient)
    (hleading_smul : ∀ (c : ZMod ℓ) (f : S),
      leadingValue (algebraMap (ZMod ℓ) S c * f) =
        c * leadingValue f)
    (hclass_normalized : leadingValue classQuotient = 1)
    (hlift_normalized : leadingValue (BL.lift F) = 1)
    (D : Derivation (ZMod ℓ) S S) (t : S)
    (A B : Polynomial (ZMod ℓ))
    (htrans : Transcendental (ZMod ℓ) t) (ht : D t ≠ 0)
    (numerator denominator : S) (hdenominator : denominator ≠ 0)
    (hquotient_of_normalized_product :
      classQuotient = BL.lift F →
        aeval t A * denominator = numerator * aeval t B)
    (hFrobenius_of_expansion :
      BL.hasProductExpansion F classQuotient →
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
        D numerator = 0 ∧ D denominator = 0)
    (hcanonical : CanonicalCongruencePrime ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    wronskianObstruction A B = 0 := by
  obtain ⟨hnormalized, hexpansion⟩ :=
    normalized_classPoly_eq_borcherdsProduct BL WV hBL hWV F
      classDivisor classQuotient leadingValue hpairing
      hnormalization_zero hpredicted_divisor CuspExponentsVanish
      hcusp_of_weyl hrigidity hleading_smul hclass_normalized
      hlift_normalized
  obtain ⟨hnumerator, hdenominatorDeriv⟩ :=
    hFrobenius_of_expansion hexpansion hcanonical hsquarefree hmod hinert
  exact wronskian_zero_of_borcherds_quotient D t A B htrans ht
    numerator denominator hdenominator
      (hquotient_of_normalized_product hnormalized)
      hnumerator hdenominatorDeriv

/-- Fully internal finite-Euler-product version of the paper's Wronskian
proposition.  The external Borcherds interface has a concrete expansion
predicate by construction.  Divisibility of every exponent is proved from
`Hn_square_coefficient_eq_zero`; factorwise Frobenius and the derivative of
the finite products are then proved internally. -/
theorem canonicalCongruence_forces_wronskian_zero_from_concrete_product
    (ℓ n : ℕ) [Fact ℓ.Prime]
    {ι Input Divisor S Theta Scalar Cusp : Type*}
    [DecidableEq ι] [Field S] [CharP S ℓ] [Algebra (ZMod ℓ) S]
    [Zero Scalar]
    (s : Finset ι) (index eplus eminus : ι → ℕ) (q : S)
    (lift : Input → S) (divisor : S → Divisor)
    (predictedDivisor : Input → Divisor)
    (hasUnitaryCharacter : S → Prop)
    (WV : WeylVectorData Input Theta Scalar Cusp)
    (hBL : BruinierOnoBorcherdsInput
      (quotientBorcherdsLiftData lift divisor predictedDivisor
        hasUnitaryCharacter
        (fun _ => ∏ i ∈ s, (1 - q ^ index i) ^ eplus i)
        (fun _ => ∏ i ∈ s, (1 - q ^ index i) ^ eminus i)))
    (hWV : BruinierSchwagenscheidtWeylInput WV)
    (F : Input) (classDivisor : Divisor)
    (t : S) (A B : Polynomial (ZMod ℓ))
    (leadingValue : S → ZMod ℓ)
    (hpairing : ∀ c : Cusp,
      WV.regularizedPairing F (WV.cuspTheta c) = 0)
    (hnormalization_zero : WV.normalization 0 = 0)
    (hpredicted_divisor : predictedDivisor F = classDivisor)
    (CuspExponentsVanish : Prop)
    (hcusp_of_weyl :
      (∀ c : Cusp, WV.weylVector F c = 0) → CuspExponentsVanish)
    (hrigidity :
      divisor (lift F) = classDivisor → CuspExponentsVanish →
        ∃ c : ZMod ℓ, lift F =
          algebraMap (ZMod ℓ) S c * (aeval t A / aeval t B))
    (hleading_smul : ∀ (c : ZMod ℓ) (f : S),
      leadingValue (algebraMap (ZMod ℓ) S c * f) =
        c * leadingValue f)
    (hclass_normalized : leadingValue (aeval t A / aeval t B) = 1)
    (hlift_normalized : leadingValue (lift F) = 1)
    (H : Analytic.HForm (ZMod ℓ)) (a : ZMod ℓ)
    (b chi : ι → ZMod ℓ)
    (hnorm : Analytic.HasHnNormalization n a H)
    (hconstant : ∀ i ∈ s, ¬ℓ ∣ index i →
      b i + H ((index i : ℤ) ^ 2) - chi i * H 1 = 0)
    (ha_of_canonical_inert :
      CanonicalCongruencePrime ℓ →
      legendreSym ℓ (-(n : ℤ)) = -1 → a = 0)
    (hb_of_canonical_inert : ∀ i ∈ s, ¬ℓ ∣ index i →
      CanonicalCongruencePrime ℓ →
      legendreSym ℓ (-(n : ℤ)) = -1 → b i = 0)
    (hexponent : ∀ i ∈ s,
      (eplus i : ZMod ℓ) - (eminus i : ZMod ℓ) =
        H ((index i : ℤ) ^ 2))
    (honeSide : ∀ i ∈ s, eplus i = 0 ∨ eminus i = 0)
    (D : Derivation (ZMod ℓ) S S)
    (htrans : Transcendental (ZMod ℓ) t) (ht : D t ≠ 0)
    (hB : aeval t B ≠ 0)
    (hproductDenominator :
      (∏ i ∈ s, (1 - q ^ index i) ^ eminus i) ≠ 0)
    (hcanonical : CanonicalCongruencePrime ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    wronskianObstruction A B = 0 := by
  let numerator : S := ∏ i ∈ s, (1 - q ^ index i) ^ eplus i
  let denominator : S := ∏ i ∈ s, (1 - q ^ index i) ^ eminus i
  have hratio : aeval t A / aeval t B = numerator / denominator := by
    dsimp [numerator, denominator]
    exact normalized_classPolynomial_quotient_eq_concrete_product
      lift divisor predictedDivisor hasUnitaryCharacter
      (fun _ => ∏ i ∈ s, (1 - q ^ index i) ^ eplus i)
      (fun _ => ∏ i ∈ s, (1 - q ^ index i) ^ eminus i)
      WV hBL hWV F classDivisor t A B leadingValue hpairing
      hnormalization_zero hpredicted_divisor CuspExponentsVanish
      hcusp_of_weyl hrigidity hleading_smul hclass_normalized
      hlift_normalized
  have hdiv : ∀ i ∈ s,
      ℓ ∣ index i ∨ (ℓ ∣ eplus i ∧ ℓ ∣ eminus i) := by
    intro i hi
    by_cases hm : ℓ ∣ index i
    · exact Or.inl hm
    · exact euler_exponents_dvd_of_Hn_square_vanishing
        ℓ n (index i) (eplus i) (eminus i) H a (b i) (chi i)
        hnorm (hconstant i hi hm) (ha_of_canonical_inert hcanonical hinert)
        (hb_of_canonical_inert i hi hm hcanonical hinert)
        (hexponent i hi) (honeSide i hi)
  have hnumerator : D numerator = 0 := by
    dsimp [numerator]
    exact derivation_finset_eulerProduct_eq_zero ℓ D q s index eplus
      (fun i hi => (hdiv i hi).imp_right And.left)
  have hdenominatorDeriv : D denominator = 0 := by
    dsimp [denominator]
    exact derivation_finset_eulerProduct_eq_zero ℓ D q s index eminus
      (fun i hi => (hdiv i hi).imp_right And.right)
  have hcross :
      aeval t A * denominator = numerator * aeval t B := by
    exact (div_eq_div_iff hB (by simpa [denominator] using
      hproductDenominator)).mp hratio
  exact wronskian_zero_of_borcherds_quotient D t A B htrans ht
    numerator denominator (by simpa [denominator] using hproductDenominator)
    hcross hnumerator hdenominatorDeriv

/-- Non-weakened formal-series form of the Wronskian proposition.  Its input
is the quotient equality produced by the normalized Borcherds product theorem
after embedding power series into Laurent series.  Cross multiplication is
performed internally and descended through the injective embedding, so no
separate product identity is postulated.  The numerator and denominator are
full infinite products, encoded by coefficient stabilization, and their
derivatives vanish by the internal square-coefficient and Frobenius
calculations above. -/
theorem canonicalCongruence_forces_wronskian_zero_from_infinite_product
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (index eplus eminus : ℕ → ℕ)
    (numerator denominator : PowerSeries (ZMod ℓ))
    (hnumeratorProduct :
      IsStabilizedEulerProduct numerator index eplus)
    (hdenominatorProduct :
      IsStabilizedEulerProduct denominator index eminus)
    (H : Analytic.HForm (ZMod ℓ)) (a : ZMod ℓ)
    (b chi : ℕ → ZMod ℓ)
    (hnorm : Analytic.HasHnNormalization n a H)
    (hconstant : ∀ i : ℕ, ¬ℓ ∣ index i →
      b i + H ((index i : ℤ) ^ 2) - chi i * H 1 = 0)
    (ha_of_canonical_inert :
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 → a = 0)
    (hb_of_canonical_inert : ∀ i : ℕ, ¬ℓ ∣ index i →
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 → b i = 0)
    (hexponent : ∀ i : ℕ,
      (eplus i : ZMod ℓ) - (eminus i : ZMod ℓ) =
        H ((index i : ℤ) ^ 2))
    (honeSide : ∀ i : ℕ, eplus i = 0 ∨ eminus i = 0)
    (t : PowerSeries (ZMod ℓ)) (A B : Polynomial (ZMod ℓ))
    (htrans : Transcendental (ZMod ℓ) t)
    (ht : PowerSeries.derivative (R := ZMod ℓ) t ≠ 0)
    (hB : aeval t B ≠ 0)
    (hdenominator : denominator ≠ 0)
    (hquotient :
      aeval (t : LaurentSeries (ZMod ℓ)) A /
          aeval (t : LaurentSeries (ZMod ℓ)) B =
        (numerator : LaurentSeries (ZMod ℓ)) /
          (denominator : LaurentSeries (ZMod ℓ)))
    (hcanonical : CanonicalCongruencePrime ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    wronskianObstruction A B = 0 := by
  have hdiv : ∀ i : ℕ,
      ℓ ∣ index i ∨ (ℓ ∣ eplus i ∧ ℓ ∣ eminus i) := by
    intro i
    by_cases hm : ℓ ∣ index i
    · exact Or.inl hm
    · exact euler_exponents_dvd_of_Hn_square_vanishing
        ℓ n (index i) (eplus i) (eminus i) H a (b i) (chi i)
        hnorm (hconstant i hm)
        (ha_of_canonical_inert hcanonical hsquarefree hmod hinert)
        (hb_of_canonical_inert i hm hcanonical hsquarefree hmod hinert)
        (hexponent i) (honeSide i)
  have hnumerator :
      PowerSeries.derivative (R := ZMod ℓ) numerator = 0 :=
    stabilizedEulerProduct_derivative_eq_zero ℓ numerator index eplus
      hnumeratorProduct (fun i => (hdiv i).imp_right And.left)
  have hdenominatorDeriv :
      PowerSeries.derivative (R := ZMod ℓ) denominator = 0 :=
    stabilizedEulerProduct_derivative_eq_zero ℓ denominator index eminus
      hdenominatorProduct (fun i => (hdiv i).imp_right And.right)
  have hproduct :
      aeval t A * denominator = numerator * aeval t B :=
    powerSeries_crossProduct_of_laurentSeries_quotient
      t numerator denominator A B hB hdenominator hquotient
  exact wronskian_zero_of_borcherds_quotient
    (PowerSeries.derivative (R := ZMod ℓ)) t A B htrans ht
    numerator denominator hdenominator hproduct
    hnumerator hdenominatorDeriv

/-- Exact infinite-product endpoint after the theta/duality argument has
already produced the square-coefficient vanishing.  In contrast with
`canonicalCongruence_forces_wronskian_zero_from_infinite_product`, this
statement does not expose the auxiliary coefficients `a`, `b`, and `chi`, a
normalization of `H`, or a constant-term identity.  It derives exponent
divisibility directly from square-coefficient vanishing, the signed-exponent
identity, and the one-sidedness of the positive and negative parts, then
performs the Frobenius, cross-multiplication, and Wronskian arguments
internally. -/
theorem canonicalCongruence_forces_wronskian_zero_from_square_vanishing
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (index eplus eminus : ℕ → ℕ)
    (numerator denominator : PowerSeries (ZMod ℓ))
    (hnumeratorProduct :
      IsStabilizedEulerProduct numerator index eplus)
    (hdenominatorProduct :
      IsStabilizedEulerProduct denominator index eminus)
    (H : Analytic.HForm (ZMod ℓ))
    (hsquareVanish : ∀ i : ℕ, ¬ℓ ∣ index i →
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
        H ((index i : ℤ) ^ 2) = 0)
    (hexponent : ∀ i : ℕ,
      (eplus i : ZMod ℓ) - (eminus i : ZMod ℓ) =
        H ((index i : ℤ) ^ 2))
    (honeSide : ∀ i : ℕ, eplus i = 0 ∨ eminus i = 0)
    (t : PowerSeries (ZMod ℓ)) (A B : Polynomial (ZMod ℓ))
    (htrans : Transcendental (ZMod ℓ) t)
    (ht : PowerSeries.derivative (R := ZMod ℓ) t ≠ 0)
    (hB : aeval t B ≠ 0)
    (hdenominator : denominator ≠ 0)
    (hquotient :
      aeval (t : LaurentSeries (ZMod ℓ)) A /
          aeval (t : LaurentSeries (ZMod ℓ)) B =
        (numerator : LaurentSeries (ZMod ℓ)) /
          (denominator : LaurentSeries (ZMod ℓ)))
    (hcanonical : CanonicalCongruencePrime ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : legendreSym ℓ (-(n : ℤ)) = -1) :
    wronskianObstruction A B = 0 := by
  have hdiv : ∀ i : ℕ,
      ℓ ∣ index i ∨ (ℓ ∣ eplus i ∧ ℓ ∣ eminus i) := by
    intro i
    by_cases hm : ℓ ∣ index i
    · exact Or.inl hm
    · exact euler_exponents_dvd_of_square_coefficient_eq_zero
        ℓ (index i) (eplus i) (eminus i) H
        (hsquareVanish i hm hcanonical hsquarefree hmod hinert)
        (hexponent i) (honeSide i)
  have hnumerator :
      PowerSeries.derivative (R := ZMod ℓ) numerator = 0 :=
    stabilizedEulerProduct_derivative_eq_zero ℓ numerator index eplus
      hnumeratorProduct (fun i => (hdiv i).imp_right And.left)
  have hdenominatorDeriv :
      PowerSeries.derivative (R := ZMod ℓ) denominator = 0 :=
    stabilizedEulerProduct_derivative_eq_zero ℓ denominator index eminus
      hdenominatorProduct (fun i => (hdiv i).imp_right And.right)
  have hproduct :
      aeval t A * denominator = numerator * aeval t B :=
    powerSeries_crossProduct_of_laurentSeries_quotient
      t numerator denominator A B hB hdenominator hquotient
  exact wronskian_zero_of_borcherds_quotient
    (PowerSeries.derivative (R := ZMod ℓ)) t A B htrans ht
    numerator denominator hdenominator hproduct
    hnumerator hdenominatorDeriv

end SptCM
