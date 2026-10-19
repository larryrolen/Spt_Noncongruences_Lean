import blessed.SptCM.Definitions
import blessed.SptCM.Analytic.ChiTwelve
import blessed.SptCM.PaperInterfaces
import blessed.SptCM.Analytic.ThetaHecke
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Paper-specific coefficient series and theta-cycle deductions

The fractional exponent `r / 24` is represented by the integer index `r`.
All congruences are expressed by reducing the integral coefficient function to
`ZMod ℓ`.  Analytic literature inputs remain explicit propositions.
-/

namespace SptCM.Analytic

open SptCM.PaperInterfaces

/-- The ordinary partition number, using Mathlib's finite type of partitions. -/
def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The coefficient `a(r)` of the smallest-parts mock modular form.
The supported nonnegative indices satisfy `r ≡ 23 (mod 24)` and correspond to
`r = 24n - 1`; the principal coefficient at `r = -1` is specified separately. -/
def aCoeff (r : ℤ) : ℤ :=
  if r = -1 then 1
  else if 0 ≤ r ∧ r % 24 = 23 then
    let n := ((r + 1).toNat / 24)
    (-12 : ℤ) * (SptCM.spt n : ℤ) - r * (partitionNumber n : ℤ)
  else 0

/-- On its positive support, `aCoeff` is exactly
`-12*spt(n) - (24n-1)*p(n)`. -/
theorem aCoeff_twentyFour_mul_sub_one (n : ℕ) (hn : 0 < n) :
    aCoeff (24 * (n : ℤ) - 1) =
      -12 * (SptCM.spt n : ℤ) -
        (24 * (n : ℤ) - 1) * (partitionNumber n : ℤ) := by
  rw [aCoeff]
  split_ifs with hneg hsupp
  · omega
  · have hnat : (24 * (n : ℤ) - 1 + 1).toNat = 24 * n := by omega
    rw [hnat, Nat.mul_div_right n (by norm_num : 0 < 24)]
  · exfalso
    apply hsupp
    constructor
    · omega
    · omega

@[simp] theorem aCoeff_neg_one : aCoeff (-1) = 1 := by
  simp [aCoeff]

/-- At a supported index divisible by `ℓ`, the partition-number summand drops
out modulo `ℓ`, leaving exactly the smallest-parts coefficient. -/
theorem aCoeff_mod_eq_neg_twelve_spt
    (ℓ n : ℕ) (hn : 0 < n) (hdiv : (ℓ : ℤ) ∣ 24 * (n : ℤ) - 1) :
    (aCoeff (24 * (n : ℤ) - 1) : ZMod ℓ) =
      (-12 : ZMod ℓ) * (SptCM.spt n : ZMod ℓ) := by
  rw [aCoeff_twentyFour_mul_sub_one n hn]
  have hzero : ((24 * (n : ℤ) - 1 : ℤ) : ZMod ℓ) = 0 := by
    rw [CharP.intCast_eq_zero_iff]
    exact_mod_cast hdiv
  have hzero' : (24 : ZMod ℓ) * (n : ZMod ℓ) - 1 = 0 := by
    simpa using hzero
  push_cast
  rw [hzero', zero_mul, sub_zero]

/-- The coefficient-function model of `f = Σ a(r) q^(r/24)`. -/
def fSeries : QSeries ℤ := aCoeff

/-- Coefficientwise reduction of `f` modulo `ℓ`. -/
def fSeriesMod (ℓ : ℕ) : QSeries (ZMod ℓ) :=
  fun r => (aCoeff r : ZMod ℓ)

/-- `Θ = q d/dq` on series indexed by the numerator of `r/24`.
Accordingly, the coefficient at index `r` is multiplied by `r/24`. -/
def thetaSeriesOp (ℓ : ℕ) [Fact ℓ.Prime] :
    QSeries (ZMod ℓ) → QSeries (ZMod ℓ) :=
  fun g r => ((r : ZMod ℓ) / (24 : ZMod ℓ)) * g r

/-- The coefficientwise closed form of the `k`-fold theta operator. -/
def thetaPowerSeriesOp (ℓ k : ℕ) [Fact ℓ.Prime] :
    QSeries (ZMod ℓ) → QSeries (ZMod ℓ) :=
  fun g r => (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ k) * g r

/-- Iterating `Θ` gives the expected power of the diagonal coefficient. -/
theorem thetaSeriesOp_iterate (ℓ k : ℕ) [Fact ℓ.Prime]
    (g : QSeries (ZMod ℓ)) :
    (thetaSeriesOp ℓ)^[k] g = thetaPowerSeriesOp ℓ k g := by
  induction k generalizing g with
  | zero =>
      funext r
      simp [thetaPowerSeriesOp]
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      funext r
      simp only [thetaSeriesOp, thetaPowerSeriesOp]
      ring

/-- At one coefficient, the theta power is diagonal with eigenvalue
`(r/24)^k`. -/
@[simp] theorem thetaPowerSeriesOp_apply (ℓ k : ℕ) [Fact ℓ.Prime]
    (g : QSeries (ZMod ℓ)) (r : ℤ) :
    thetaPowerSeriesOp ℓ k g r =
      (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ k) * g r := rfl

/-- The `U_ℓ` operator on the integral-index coefficient model. -/
def uSeriesOp {R : Type*} (ℓ : ℕ) (g : QSeries R) : QSeries R :=
  fun r => g ((ℓ : ℤ) * r)

@[simp] theorem uSeriesOp_apply {R : Type*} (ℓ : ℕ) (g : QSeries R) (r : ℤ) :
    uSeriesOp ℓ g r = g ((ℓ : ℤ) * r) := rfl

/-- The exact elementary coefficient bridge needed to identify canonical
smallest-parts congruences with `U_ℓ`-vanishing.  Its proof is the remaining
integer reindexing/substitution calculation involving `canonicalResidue`. -/
def CanonicalUCoefficientInput (ℓ : ℕ) : Prop :=
  SptCM.CanonicalCongruencePrime ℓ ↔
    ∀ r : ℤ, fSeriesMod ℓ ((ℓ : ℤ) * r) = 0

/-- The custom `Nat.modInv` used by the project really is the inverse of 24
modulo every prime `ℓ ≥ 5`. -/
theorem canonicalResidue_mul_eq_one_zmod
    (ℓ : ℕ) (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ) :
    (24 : ZMod ℓ) * (SptCM.canonicalResidue ℓ : ZMod ℓ) = 1 := by
  have hcop : Nat.Coprime 24 ℓ := by
    exact ((hprime.coprime_iff_not_dvd).2 (by
      intro hd
      have hle : ℓ ≤ 24 := Nat.le_of_dvd (by norm_num) hd
      interval_cases ℓ
      all_goals norm_num at hprime
      all_goals norm_num at hd)).symm
  have hgcd : Nat.gcd 24 ℓ = 1 := hcop.gcd_eq_one
  have hrep :
      (SptCM.canonicalResidue ℓ : ZMod ℓ) =
        (Nat.gcdA 24 ℓ : ZMod ℓ) := by
    rw [SptCM.canonicalResidue, Nat.modInv]
    have hpos : (0 : ℤ) < (ℓ : ℤ) := by omega
    have hnonneg : 0 ≤ Nat.gcdA 24 ℓ % (ℓ : ℤ) :=
      Int.emod_nonneg _ hpos.ne'
    rw [← ZMod.intCast_mod (Nat.gcdA 24 ℓ) ℓ]
    have heq : (((Nat.gcdA 24 ℓ % (ℓ : ℤ)).toNat : ℕ) : ℤ) =
        Nat.gcdA 24 ℓ % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    calc
      ((Nat.gcdA 24 ℓ % (ℓ : ℤ)).toNat : ZMod ℓ) =
          ((((Nat.gcdA 24 ℓ % (ℓ : ℤ)).toNat : ℕ) : ℤ) : ZMod ℓ) := by
            norm_cast
      _ = (Nat.gcdA 24 ℓ % (ℓ : ℤ) : ZMod ℓ) :=
        congrArg (fun z : ℤ => (z : ZMod ℓ)) heq
  rw [hrep]
  have hbez := Nat.gcd_eq_gcd_ab 24 ℓ
  rw [hgcd] at hbez
  have hz : (24 : ZMod ℓ) * (Nat.gcdA 24 ℓ : ZMod ℓ) +
      (ℓ : ZMod ℓ) * (Nat.gcdB 24 ℓ : ZMod ℓ) = 1 := by
    have hz' := congrArg (fun z : ℤ => (z : ZMod ℓ)) hbez.symm
    push_cast at hz'
    simpa using hz'
  simpa using hz

/-- The chosen representative of the inverse lies in the standard range. -/
theorem canonicalResidue_lt
    (ℓ : ℕ) (hpos : 0 < ℓ) :
    SptCM.canonicalResidue ℓ < ℓ := by
  rw [SptCM.canonicalResidue, Nat.modInv]
  have hnonneg : 0 ≤ Nat.gcdA 24 ℓ % (ℓ : ℤ) :=
    Int.emod_nonneg _ (by omega)
  have hlt : Nat.gcdA 24 ℓ % (ℓ : ℤ) < (ℓ : ℤ) :=
    Int.emod_lt_of_pos _ (by omega)
  have heq : (((Nat.gcdA 24 ℓ % (ℓ : ℤ)).toNat : ℕ) : ℤ) =
      Nat.gcdA 24 ℓ % (ℓ : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  omega

/-- An index is in the canonical residue class exactly when its normalized
Fourier numerator `24n-1` is divisible by `ℓ`. -/
theorem dvd_twentyFour_mul_sub_one_iff_mod_canonicalResidue
    (ℓ n : ℕ) (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ) :
    (ℓ : ℤ) ∣ 24 * (n : ℤ) - 1 ↔
      (n : ZMod ℓ) = (SptCM.canonicalResidue ℓ : ZMod ℓ) := by
  have hinv := canonicalResidue_mul_eq_one_zmod ℓ hprime hfive
  constructor
  · intro hdiv
    have hn : (24 : ZMod ℓ) * (n : ZMod ℓ) = 1 := by
      have hz : ((24 * (n : ℤ) - 1 : ℤ) : ZMod ℓ) = 0 := by
        rw [CharP.intCast_eq_zero_iff]
        exact hdiv
      push_cast at hz
      linear_combination hz
    calc
      (n : ZMod ℓ) = 1 * n := by ring
      _ = ((24 : ZMod ℓ) * SptCM.canonicalResidue ℓ) * n := by rw [hinv]
      _ = (SptCM.canonicalResidue ℓ : ZMod ℓ) *
          ((24 : ZMod ℓ) * n) := by ring
      _ = SptCM.canonicalResidue ℓ := by rw [hn]; ring
  · intro hn
    rw [← CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ]
    push_cast
    rw [hn]
    linear_combination hinv

/-- Natural-number reindexing of the canonical residue class. -/
theorem eq_mul_add_canonicalResidue_of_dvd
    (ℓ n : ℕ) (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ)
    (hdiv : (ℓ : ℤ) ∣ 24 * (n : ℤ) - 1) :
    ∃ k : ℕ, n = ℓ * k + SptCM.canonicalResidue ℓ := by
  have heq := (dvd_twentyFour_mul_sub_one_iff_mod_canonicalResidue
    ℓ n hprime hfive).mp hdiv
  have hmod : n % ℓ = SptCM.canonicalResidue ℓ % ℓ :=
    (ZMod.natCast_eq_natCast_iff' n (SptCM.canonicalResidue ℓ) ℓ).mp heq
  have hb : SptCM.canonicalResidue ℓ < ℓ :=
    canonicalResidue_lt ℓ hprime.pos
  refine ⟨n / ℓ, ?_⟩
  nth_rewrite 1 [← Nat.mod_add_div n ℓ]
  rw [hmod, Nat.mod_eq_of_lt hb]
  omega

/-- Canonicality is equivalent to vanishing of the reduced mock series after
`U_ℓ`, once the explicit coefficient bridge has been established. -/
theorem canonicalCongruencePrime_iff_uSeriesOp_eq_zero
    (ℓ : ℕ) (hcoeff : CanonicalUCoefficientInput ℓ) :
    SptCM.CanonicalCongruencePrime ℓ ↔
      uSeriesOp ℓ (fSeriesMod ℓ) = 0 := by
  rw [CanonicalUCoefficientInput] at hcoeff
  rw [hcoeff]
  constructor
  · intro h
    funext r
    exact h r
  · intro h r
    have := congrFun h r
    simpa using this

/-- The complete internal coefficient calculation: for a prime `ℓ ≥ 5`, the
canonical smallest-parts congruence is equivalent to coefficientwise
`U_ℓ`-vanishing of the reduced mock series. -/
theorem canonicalCongruencePrime_iff_uSeriesOp_eq_zero_exact
    (ℓ : ℕ) (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ) :
    SptCM.CanonicalCongruencePrime ℓ ↔
      uSeriesOp ℓ (fSeriesMod ℓ) = 0 := by
  letI : Fact ℓ.Prime := ⟨hprime⟩
  constructor
  · intro hcanonical
    funext r
    simp only [uSeriesOp_apply, fSeriesMod, Pi.zero_apply]
    let x : ℤ := (ℓ : ℤ) * r
    change (aCoeff x : ZMod ℓ) = 0
    rw [aCoeff]
    split_ifs with hminus hsupp
    · have hd : (ℓ : ℤ) ∣ 1 := by
        refine ⟨-r, ?_⟩
        dsimp [x] at hminus ⊢
        rw [mul_neg, hminus]
        norm_num
      have : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd
      omega
    · let n : ℕ := (x + 1).toNat / 24
      have hx : x = 24 * (n : ℤ) - 1 := by
        have hnonneg : 0 ≤ x + 1 := by omega
        have hd24 : (24 : ℤ) ∣ x + 1 := by
          rw [Int.dvd_iff_emod_eq_zero]
          omega
        rcases hd24 with ⟨z, hz⟩
        have hznonneg : 0 ≤ z := by omega
        have hnat : (x + 1).toNat = 24 * z.toNat := by
          apply Nat.cast_injective (R := ℤ)
          push_cast
          rw [Int.toNat_of_nonneg hnonneg, Int.toNat_of_nonneg hznonneg]
          omega
        dsimp [n]
        rw [hnat]
        push_cast
        rw [Int.mul_ediv_cancel_left _ (by norm_num : (24 : ℤ) ≠ 0)]
        rw [Int.toNat_of_nonneg hznonneg]
        omega
      have hell : (ℓ : ℤ) ∣ 24 * (n : ℤ) - 1 := by
        rw [← hx]
        exact ⟨r, rfl⟩
      obtain ⟨k, hk⟩ :=
        eq_mul_add_canonicalResidue_of_dvd ℓ n hprime hfive hell
      have hnpos : 0 < n := by
        dsimp [n]
        omega
      have hspt : (SptCM.spt n : ZMod ℓ) = 0 := by
        rw [hk, CharP.cast_eq_zero_iff]
        exact hcanonical.dvd_spt k
      change (((-12 : ℤ) * (SptCM.spt n : ℤ) -
        x * (partitionNumber n : ℤ) : ℤ) : ZMod ℓ) = 0
      have hxzero : (x : ZMod ℓ) = 0 := by
        dsimp [x]
        simp
      push_cast
      rw [hspt, hxzero]
      ring
    · simp
  · intro hu
    refine ⟨hprime, hfive, ?_⟩
    intro k
    let n : ℕ := ℓ * k + SptCM.canonicalResidue ℓ
    have hncast :
        (n : ZMod ℓ) = (SptCM.canonicalResidue ℓ : ZMod ℓ) := by
      dsimp [n]
      push_cast
      simp
    have hell : (ℓ : ℤ) ∣ 24 * (n : ℤ) - 1 :=
      (dvd_twentyFour_mul_sub_one_iff_mod_canonicalResidue
        ℓ n hprime hfive).2 hncast
    have hbpos : 0 < SptCM.canonicalResidue ℓ := by
      by_contra hb
      have hbzero : SptCM.canonicalResidue ℓ = 0 := by omega
      change Nat.modInv 24 ℓ = 0 at hbzero
      have hinv := canonicalResidue_mul_eq_one_zmod ℓ hprime hfive
      have hzeroone : (0 : ZMod ℓ) = 1 := by
        simpa [hbzero] using hinv
      exact zero_ne_one hzeroone
    have hnpos : 0 < n := by
      dsimp [n]
      exact Nat.add_pos_right _ hbpos
    rcases hell with ⟨r, hr⟩
    have hU := congrFun hu r
    simp only [uSeriesOp_apply, fSeriesMod, Pi.zero_apply] at hU
    have hcoeff :
        (aCoeff (24 * (n : ℤ) - 1) : ZMod ℓ) = 0 := by
      rw [hr]
      exact hU
    rw [aCoeff_mod_eq_neg_twelve_spt ℓ n hnpos ⟨r, hr⟩] at hcoeff
    have htwelve : (-12 : ZMod ℓ) ≠ 0 := by
      intro hzero
      have hd : (ℓ : ℤ) ∣ (-12 : ℤ) := by
        rw [← CharP.intCast_eq_zero_iff (R := ZMod ℓ)]
        simpa using hzero
      have hd' : (ℓ : ℤ) ∣ 12 := by
        simpa using dvd_neg.mpr hd
      have hle : (ℓ : ℤ) ≤ 12 := Int.le_of_dvd (by norm_num) hd'
      have hle' : ℓ ≤ 12 := by exact_mod_cast hle
      interval_cases ℓ
      all_goals norm_num at hprime
      all_goals norm_num at hd
    have hspt : (SptCM.spt n : ZMod ℓ) = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_left htwelve
    rw [CharP.cast_eq_zero_iff] at hspt
    simpa [n] using hspt

/-- The scalar `(-24/ℓ)` appearing in the theta-cycle theorem. -/
def thetaCycleEigenvalue (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  (legendreSym ℓ (-24) : ℤ)

/-- The precise conditional form of the Ahlgren--Kim input consumed by the
paper: reduced `U_ℓ`-vanishing implies the stated theta-cycle eigenrelation. -/
def AhlgrenKimThetaCycleFromUInput (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  uSeriesOp ℓ (fSeriesMod ℓ) = 0 →
    PaperInterfaces.AhlgrenKimThetaCycleInput ℓ
      (thetaPowerSeriesOp ℓ ((ℓ - 1) / 2))
      (thetaCycleEigenvalue ℓ) (fSeriesMod ℓ)

/-- The paper's theta-cycle consequence, obtained directly from the precise
Ahlgren--Kim proposition after its `U`-vanishing hypothesis has been supplied.
The cited theorem remains an explicit argument. -/
theorem theta_cycle_of_ahlgrenKim
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hAK : PaperInterfaces.AhlgrenKimThetaCycleInput ℓ
      (thetaPowerSeriesOp ℓ ((ℓ - 1) / 2))
      (thetaCycleEigenvalue ℓ) (fSeriesMod ℓ)) :
    thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (fSeriesMod ℓ) =
      thetaCycleEigenvalue ℓ • fSeriesMod ℓ :=
  hAK

/-- Canonicality supplies the `U`-vanishing hypothesis of the exact
Ahlgren--Kim input. -/
theorem theta_cycle_of_canonical
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hcoeff : CanonicalUCoefficientInput ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ) :
    thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (fSeriesMod ℓ) =
      thetaCycleEigenvalue ℓ • fSeriesMod ℓ := by
  apply theta_cycle_of_ahlgrenKim ℓ
  apply hAK
  exact (canonicalCongruencePrime_iff_uSeriesOp_eq_zero ℓ hcoeff).mp hcanonical

/-- Canonicality supplies the `U_ℓ`-vanishing hypothesis by the internal
coefficient calculation, so the Ahlgren--Kim theta cycle needs no separate
coefficient-reindexing premise.  The only remaining hypothesis is the cited
Ahlgren--Kim implication itself. -/
theorem theta_cycle_of_canonical_exact
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ) :
    thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (fSeriesMod ℓ) =
      thetaCycleEigenvalue ℓ • fSeriesMod ℓ := by
  apply theta_cycle_of_ahlgrenKim ℓ
  apply hAK
  exact (canonicalCongruencePrime_iff_uSeriesOp_eq_zero_exact
    ℓ hcanonical.prime hcanonical.five_le).mp hcanonical

/-- The exact Euler-criterion calculation used at inert indices.  It is kept
separate from the cited theta-cycle input so that no analytic assertion is
hidden inside the coefficient argument. -/
def EulerInertMismatchInput (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ r : ℤ, legendreSym ℓ (-r) = -1 →
    (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)) ≠
      thetaCycleEigenvalue ℓ

/-- A coefficient with diagonal theta eigenvalue different from the cycle
scalar vanishes.  Euler's criterion supplies `hmismatch` at inert indices. -/
theorem aCoeff_mod_eq_zero_of_theta_cycle
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℤ)
    (hcycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (fSeriesMod ℓ) =
      thetaCycleEigenvalue ℓ • fSeriesMod ℓ)
    (hmismatch : (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)) ≠
      thetaCycleEigenvalue ℓ) :
    (aCoeff r : ZMod ℓ) = 0 := by
  have hr := congrFun hcycle r
  simp only [thetaPowerSeriesOp_apply, Pi.smul_apply, smul_eq_mul,
    fSeriesMod] at hr
  have hmul :
      ((((r : ZMod ℓ) / 24) ^ ((ℓ - 1) / 2)) - thetaCycleEigenvalue ℓ) *
        (aCoeff r : ZMod ℓ) = 0 := by
    linear_combination hr
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hmismatch)

/-- Inert mock coefficients vanish, with Euler's criterion exposed as its
precise elementary input. -/
theorem aCoeff_mod_eq_zero_of_inert
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℤ)
    (hcycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) (fSeriesMod ℓ) =
      thetaCycleEigenvalue ℓ • fSeriesMod ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-r) = -1) :
    (aCoeff r : ZMod ℓ) = 0 :=
  aCoeff_mod_eq_zero_of_theta_cycle ℓ r hcycle (hEuler r hinert)

/-- The paper's mock coefficient vanishing with canonicality as the only
paper-internal hypothesis.  Exact `U_ℓ`-vanishing is proved coefficientwise,
the cited Ahlgren--Kim implication supplies the theta cycle, and Euler's
criterion supplies the inert mismatch. -/
theorem aCoeff_mod_eq_zero_of_canonical_inert_exact
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℤ)
    (hcanonical : SptCM.CanonicalCongruencePrime ℓ)
    (hAK : AhlgrenKimThetaCycleFromUInput ℓ)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-r) = -1) :
    (aCoeff r : ZMod ℓ) = 0 :=
  aCoeff_mod_eq_zero_of_inert ℓ r
    (theta_cycle_of_canonical_exact ℓ hcanonical hAK) hEuler hinert

/-- Exact coefficientwise condition under which a diagonal operator commutes
with the weight `3/2` Hecke operator. -/
theorem heckeThreeHalf_commutes_with_diagonal
    {K : Type*} [Field K]
    (p : ℕ) (chiP : K) (legendre : ℤ → K) (weight : ℤ → K)
    (hup : ∀ n : ℤ, weight (((p : ℤ) ^ 2) * n) = weight n)
    (hdown : ∀ n : ℤ, ((p : ℤ) ^ 2) ∣ n →
      weight (n / (p : ℤ) ^ 2) = weight n) :
    (fun g n => weight n * heckeThreeHalf p chiP legendre g n) =
      (fun g => heckeThreeHalf p chiP legendre (fun n => weight n * g n)) := by
  funext g n
  simp only [heckeThreeHalf]
  by_cases hdiv : ((p : ℤ) ^ 2) ∣ n
  · rw [if_pos hdiv, if_pos hdiv, hup, hdown n hdiv]
    ring
  · rw [if_neg hdiv, if_neg hdiv, hup]
    ring

/-- Paper-specialized theta/Hecke commutation from the two elementary index
weight identities.  These identities are the finite-field calculation using
`p ≠ ℓ` and Fermat's theorem. -/
theorem heckeThetaCycleCommute_of_weight_relations
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (chiP : ZMod ℓ) (legendre : ℤ → ZMod ℓ)
    (hup : ∀ n : ℤ,
      ((((p : ℤ) ^ 2 * n : ℤ) : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2) =
        (((n : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)))
    (hdown : ∀ n : ℤ, ((p : ℤ) ^ 2) ∣ n →
      ((((n / ((p : ℤ) ^ 2) : ℤ) : ZMod ℓ) / (24 : ZMod ℓ)) ^
        ((ℓ - 1) / 2)) =
        (((n : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2))) :
    (fun g => thetaPowerSeriesOp ℓ ((ℓ - 1) / 2)
      (heckeThreeHalf p chiP legendre g)) =
    (fun g => heckeThreeHalf p chiP legendre
      (thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) g)) := by
  exact heckeThreeHalf_commutes_with_diagonal p chiP legendre
    (fun n => (((n : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2))) hup hdown

/-- The inert-coefficient deduction for any grid series satisfying the same
theta-cycle eigenrelation. -/
theorem gridCoeff_eq_zero_of_theta_cycle
    (ℓ : ℕ) [Fact ℓ.Prime] (G : QSeries (ZMod ℓ)) (r : ℤ)
    (hcycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) G =
      thetaCycleEigenvalue ℓ • G)
    (hmismatch : (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)) ≠
      thetaCycleEigenvalue ℓ) :
    G r = 0 := by
  have hr := congrFun hcycle r
  simp only [thetaPowerSeriesOp_apply, Pi.smul_apply, smul_eq_mul] at hr
  have hmul :
      ((((r : ZMod ℓ) / 24) ^ ((ℓ - 1) / 2)) - thetaCycleEigenvalue ℓ) *
        G r = 0 := by
    linear_combination hr
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hmismatch)

/-- Inert grid coefficients vanish from grid theta support and the same
Euler-criterion mismatch used for the mock form. -/
theorem gridCoeff_eq_zero_of_inert
    (ℓ : ℕ) [Fact ℓ.Prime] (G : QSeries (ZMod ℓ)) (r : ℤ)
    (hcycle : thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) G =
      thetaCycleEigenvalue ℓ • G)
    (hEuler : EulerInertMismatchInput ℓ)
    (hinert : legendreSym ℓ (-r) = -1) :
    G r = 0 :=
  gridCoeff_eq_zero_of_theta_cycle ℓ G r hcycle (hEuler r hinert)

end SptCM.Analytic
