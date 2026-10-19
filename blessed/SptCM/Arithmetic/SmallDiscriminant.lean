import blessed.SptCM.Lemmas.SmallDiscriminantArithmetic
import blessed.SptCM.PaperInterfaces
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The small discriminant argument

This module separates the cited analytic character estimate from the elementary
minimality, squarefreeness, and degree-bound deductions made in Section 7.
The only analytic datum is a bounded first inert member of the progression.
-/

namespace SptCM

/-- The bounded first nonresidue furnished by Treviño's corrected character
estimate together with the explicit numerical estimate in the paper.  The last
field records the defining minimality of the chosen member of the progression. -/
def SmallInertCandidateInput : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → cutoff ≤ ℓ → ∃ n : ℕ,
    0 < n ∧ n % 24 = 23 ∧ ¬ IsSquare (-(n : ZMod ℓ)) ∧
      (n + 1) ^ 2 < 24 * ℓ ∧
      ∀ m : ℕ, 0 < m → m < n →
        ¬ (m % 24 = 23 ∧ ¬ IsSquare (-(m : ZMod ℓ)))

/-- Removing a prime-square divisor preserves the progression and inertness
conditions used in the paper's minimality argument. -/
def PrimeSquareInvarianceInput : Prop :=
  ∀ (ℓ n p q : ℕ), ℓ.Prime → p.Prime → n = p ^ 2 * q →
    n % 24 = 23 → ¬ IsSquare (-(n : ZMod ℓ)) →
    q % 24 = 23 ∧ ¬ IsSquare (-(q : ZMod ℓ))

/-- Removing a prime-square factor really does preserve the two conditions;
this is an elementary internal deduction, not an external input. -/
theorem primeSquare_invariance
    {ℓ n p q : ℕ} (hp : p.Prime) (hfactor : n = p ^ 2 * q)
    (hnmod : n % 24 = 23) (hinert : ¬ IsSquare (-(n : ZMod ℓ))) :
    q % 24 = 23 ∧ ¬ IsSquare (-(q : ZMod ℓ)) := by
  have hpnot : ¬ p ∣ 24 := by
    intro hd
    have hp_le : p ≤ 24 := Nat.le_of_dvd (by omega) hd
    interval_cases p <;> norm_num at hp <;> omega
  have hpsq : p ^ 2 % 24 = 1 := by
    have hcop : p.Coprime 24 := (hp.coprime_iff_not_dvd).2 hpnot
    have hrcop : (p % 24).Coprime 24 :=
      (ZMod.coprime_mod_iff_coprime p 24).2 hcop
    have hrlt : p % 24 < 24 := Nat.mod_lt _ (by omega)
    generalize hr : p % 24 = r at hrcop hrlt ⊢
    interval_cases r <;> norm_num at hrcop
    all_goals simp [pow_two, Nat.mul_mod, hr]
  constructor
  · have hmodmul :
        n % 24 = (p ^ 2 % 24) * (q % 24) % 24 := by
      rw [hfactor, Nat.mul_mod]
    rw [hpsq] at hmodmul
    omega
  · intro hsq
    rcases hsq with ⟨x, hx⟩
    apply hinert
    refine ⟨(p : ZMod ℓ) * x, ?_⟩
    calc
      -(n : ZMod ℓ) = (p : ZMod ℓ) ^ 2 * (-(q : ZMod ℓ)) := by
        rw [hfactor]
        simp only [Nat.cast_mul, Nat.cast_pow]
        ring
      _ = (p : ZMod ℓ) * x * ((p : ZMod ℓ) * x) := by
        rw [hx]
        ring

/-- The prime-square invariance package required by the minimality lemma. -/
theorem primeSquareInvarianceInput : PrimeSquareInvarianceInput := by
  intro ℓ n p q _ hp hfactor hnmod hinert
  exact primeSquare_invariance hp hfactor hnmod hinert

/-- The elementary reduced-form estimate used in the paper, isolated from the
choice of the discriminant. -/
def ClassNumberEstimateInput (h : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 23 ≤ n → Squarefree n → n % 24 = 23 → 0 < h n ∧ h n < n

/-- Treviño's bounded candidate, prime-square invariance, and the reduced-form
class-number estimate imply the small-discriminant package used in the final
argument. -/
theorem smallDiscriminantInput_of_components
    (h : ℕ → ℕ)
    (hcandidate : SmallInertCandidateInput)
    (hinvariance : PrimeSquareInvarianceInput)
    (hclass : ClassNumberEstimateInput h) :
    SmallDiscriminantInput h := by
  intro ℓ hprime hlarge
  obtain ⟨n, hnpos, hnmod, hinert, hsq, hminimal⟩ :=
    hcandidate ℓ hprime hlarge
  have hsquarefree : Squarefree n := by
    apply squarefree_of_minimal_congruence_character
      (fun m => m % 24 = 23)
      (fun m => ¬ IsSquare (-(m : ZMod ℓ)))
      hnpos hnmod hinert hminimal
    · intro p q hp hfactor
      exact (hinvariance ℓ n p q hprime hp hfactor hnmod hinert).1
    · intro p q hp hfactor
      exact (hinvariance ℓ n p q hprime hp hfactor hnmod hinert).2
  have hn23 : 23 ≤ n := by omega
  have hh := hclass n hn23 hsquarefree hnmod
  have hhpos : 0 < h n := hh.1
  have hh_lt_n : h n < n := hh.2
  have hℓ96 : 96 < ℓ := by
    have : 96 < cutoff := by norm_num [cutoff]
    omega
  have hdegree_lt : 2 * h n < ℓ :=
    two_classNumber_lt_modulus hℓ96 hsq hh_lt_n
  have hdegree_pos : 0 < 2 * h n := by omega
  exact ⟨n, ⟨hsquarefree, hnmod, hinert⟩, hsq, hdegree_pos, hdegree_lt⟩

end SptCM

namespace SptCM

/-! ## First nonresidue and the elementary tail of the argument -/

/-- The first positive index at which the progression character differs from
one.  It is zero only when no such positive index exists. -/
noncomputable def firstNonresidue (ℓ : ℕ) [Fact ℓ.Prime] : ℕ := by
  classical
  exact if h : ∃ k : ℕ, 0 < k ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (k : ℤ)) ≠ 1 then
    Nat.find h
  else 0

/-- The least nonnegative representative of `24⁻¹ (mod ℓ)`. -/
noncomputable def inverse24Index (ℓ : ℕ) [NeZero ℓ] : ℕ :=
  ((24 : ZMod ℓ)⁻¹).val

/-- At every modulus in the paper's range, the inverse representative is
positive and is genuinely inverse to `24`. -/
theorem inverse24Index_spec
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : cutoff ≤ ℓ) :
    0 < inverse24Index ℓ ∧
      (24 : ZMod ℓ) * (inverse24Index ℓ : ZMod ℓ) = 1 := by
  have hℓ24 : 24 < ℓ := by
    have : 24 < cutoff := by norm_num [cutoff]
    omega
  have h24 : (24 : ZMod ℓ) ≠ 0 := by
    intro hz
    have hdvd : ℓ ∣ 24 := (ZMod.natCast_eq_zero_iff 24 ℓ).mp hz
    have := Nat.le_of_dvd (by omega : 0 < 24) hdvd
    omega
  have hcast :
      (inverse24Index ℓ : ZMod ℓ) = (24 : ZMod ℓ)⁻¹ :=
    ZMod.natCast_zmod_val _
  constructor
  · by_contra hz
    have hzero : inverse24Index ℓ = 0 := Nat.eq_zero_of_not_pos hz
    have hinvzero : ((24 : ZMod ℓ)⁻¹) = 0 := by
      rw [← hcast, hzero]
      simp
    exact inv_ne_zero h24 hinvzero
  · rw [hcast]
    exact mul_inv_cancel₀ h24

/-- The progression necessarily contains an exceptional positive index:
the inverse of `24` makes the numerator zero modulo `ℓ`. -/
theorem firstNonresidue_exists
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : cutoff ≤ ℓ) :
    ∃ k : ℕ, 0 < k ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (k : ℤ)) ≠ 1 := by
  obtain ⟨hkpos, hkinv⟩ := inverse24Index_spec hlarge
  refine ⟨inverse24Index ℓ, hkpos, ?_⟩
  have hzero :
      (((1 : ℤ) - 24 * (inverse24Index ℓ : ℤ) : ℤ) : ZMod ℓ) = 0 := by
    push_cast
    rw [hkinv]
    ring
  have hsymzero :
      legendreSym ℓ ((1 : ℤ) - 24 * (inverse24Index ℓ : ℤ)) = 0 :=
    (legendreSym.eq_zero_iff ℓ _).2 hzero
  omega

/-- The chosen first index is positive and exceptional whenever an exceptional
index exists. -/
theorem firstNonresidue_spec
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hex : ∃ k : ℕ, 0 < k ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (k : ℤ)) ≠ 1) :
    0 < firstNonresidue ℓ ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (firstNonresidue ℓ : ℤ)) ≠ 1 := by
  rw [firstNonresidue, dif_pos hex]
  exact Nat.find_spec hex

/-- Before the first exceptional index, the progression character is one. -/
theorem character_interval_progression
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hex : ∃ k : ℕ, 0 < k ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (k : ℤ)) ≠ 1)
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < firstNonresidue ℓ) :
    legendreSym ℓ ((1 : ℤ) - 24 * (j : ℤ)) = 1 := by
  rw [firstNonresidue, dif_pos hex] at hjlt
  by_contra hj
  have hle : Nat.find hex ≤ j := Nat.find_min' hex ⟨hjpos, hj⟩
  omega

/-- Shifted form of the constant-character interval used in the paper.
If `c` represents `24⁻¹ (mod ℓ)`, then every integer `j - c` with
`1 ≤ j < k` has the same Legendre symbol as `-24`. -/
theorem character_interval
    {ℓ : ℕ} [Fact ℓ.Prime] (c : ℤ)
    (hc : (24 : ZMod ℓ) * (c : ZMod ℓ) = 1)
    (hex : ∃ k : ℕ, 0 < k ∧
      legendreSym ℓ ((1 : ℤ) - 24 * (k : ℤ)) ≠ 1)
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < firstNonresidue ℓ) :
    legendreSym ℓ ((j : ℤ) - c) = legendreSym ℓ (-24) := by
  have hjchar := character_interval_progression hex hjpos hjlt
  have hcast :
      (((-24 : ℤ) * ((j : ℤ) - c) : ℤ) : ZMod ℓ) =
        (((1 : ℤ) - 24 * (j : ℤ) : ℤ) : ZMod ℓ) := by
    push_cast
    rw [mul_sub]
    rw [neg_mul, neg_mul, hc]
    ring
  have hsym :
      legendreSym ℓ ((-24 : ℤ) * ((j : ℤ) - c)) =
        legendreSym ℓ ((1 : ℤ) - 24 * (j : ℤ)) := by
    simp only [legendreSym]
    exact congrArg (fun z : ZMod ℓ => quadraticChar (ZMod ℓ) z) hcast
  rw [legendreSym.mul] at hsym
  rw [hjchar] at hsym
  have h24 : (24 : ZMod ℓ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hc
    exact zero_ne_one hc
  have hm24 : ((-24 : ℤ) : ZMod ℓ) ≠ 0 := by
    push_cast
    simpa using h24
  rcases legendreSym.eq_one_or_neg_one ℓ hm24 with ha | ha
  · rw [ha] at hsym ⊢
    simpa using hsym
  · rw [ha] at hsym ⊢
    omega

/-- Abstract statement of Treviño's corrected estimate.  `B ℓ` is the
integer upper bound for the length of a constant interval of the relevant
nonprincipal quadratic character.  This is the sole cited analytic premise
in this module. -/
def TrevinoCorrectedInput (B : ℕ → ℕ) : Prop :=
  ∀ (ℓ k : ℕ) (χ : ℕ → ℤ), ℓ.Prime → cutoff ≤ ℓ →
    (∀ j : ℕ, 0 < j → j < k → χ j = 1) → k - 1 ≤ B ℓ

/-- Treviño's interval estimate bounds the first exceptional index by one
more than its interval-length bound. -/
theorem firstNonresidue_bound_nat
    (B : ℕ → ℕ) (hTrevino : TrevinoCorrectedInput B)
    {ℓ k : ℕ} (hprime : ℓ.Prime) (hlarge : cutoff ≤ ℓ)
    (χ : ℕ → ℤ) (hkpos : 0 < k)
    (hinterval : ∀ j : ℕ, 0 < j → j < k → χ j = 1) :
    k ≤ B ℓ + 1 := by
  have h := hTrevino ℓ k χ hprime hlarge hinterval
  omega

/-- The paper's exact `3.38` bound for the first exceptional progression
index, deduced directly from Treviño's corrected real-valued estimate. -/
theorem firstNonresidue_bound
    (Nonprincipal : ℕ → (ℤ → ℤ) → Prop)
    (hTrevino :
      PaperInterfaces.TrevinoCorrectedCharacterBound Nonprincipal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : cutoff ≤ ℓ)
    (hnonprincipal : Nonprincipal ℓ (legendreSym ℓ)) :
    (firstNonresidue ℓ : ℝ) ≤
      3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 1 := by
  let c : ℤ := inverse24Index ℓ
  have hc : (24 : ZMod ℓ) * (c : ZMod ℓ) = 1 := by
    dsimp [c]
    simpa only [Int.cast_natCast] using (inverse24Index_spec hlarge).2
  have hex := firstNonresidue_exists hlarge
  let k := firstNonresidue ℓ
  have hkpos : 0 < k := (firstNonresidue_spec hex).1
  have hconstant :
      PaperInterfaces.ConstantOnInterval (legendreSym ℓ)
        (1 - c) (k - 1) := by
    intro i j hi hj
    have hi' : i + 1 < k := by omega
    have hj' : j + 1 < k := by omega
    have hci := character_interval c hc hex (Nat.succ_pos i) hi'
    have hcj := character_interval c hc hex (Nat.succ_pos j) hj'
    convert hci.trans hcj.symm using 1 <;>
      push_cast <;> ring
  have hbound :=
    hTrevino ℓ (k - 1) (legendreSym ℓ) (1 - c)
      (Fact.out : ℓ.Prime) hnonprincipal hconstant
  have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    norm_cast
    omega
  dsimp [k] at hbound ⊢
  rw [← hkcast]
  linarith

/-- Integer-cleared numerical cutoff step.  Once the explicit analytic bound
has been verified to lie below the square-root cutoff, every index below it
produces the required discriminant bound. -/
theorem numeric_cutoff_of_bound
    {ℓ k K : ℕ} (hkpos : 0 < k) (hk : k ≤ K)
    (hcutoff : (24 * K) ^ 2 < 24 * ℓ) :
    let n := 24 * k - 1
    0 < n ∧ n + 1 = 24 * k ∧ (n + 1) ^ 2 < 24 * ℓ := by
  dsimp
  have hk24 : 1 ≤ 24 * k := by omega
  have hnadd : 24 * k - 1 + 1 = 24 * k := Nat.sub_add_cancel hk24
  constructor
  · omega
  constructor
  · exact hnadd
  · rw [hnadd]
    nlinarith

/-- A purely integral index cutoff lying strictly below
`√(24ℓ)/24`; using `Nat.sqrt` avoids real-analysis side conditions. -/
def explicitCutoffIndex (ℓ : ℕ) : ℕ :=
  (Nat.sqrt (24 * ℓ) - 1) / 24

/-- The explicit integral cutoff automatically satisfies the square-root
inequality for every positive modulus. -/
theorem numeric_cutoff_integral
    {ℓ k : ℕ} (hℓ : 0 < ℓ) (hkpos : 0 < k)
    (hk : k ≤ explicitCutoffIndex ℓ) :
    let n := 24 * k - 1
    0 < n ∧ n + 1 = 24 * k ∧ (n + 1) ^ 2 < 24 * ℓ := by
  apply numeric_cutoff_of_bound hkpos hk
  unfold explicitCutoffIndex
  let s := Nat.sqrt (24 * ℓ)
  have hspos : 0 < s := by
    dsimp [s]
    exact Nat.sqrt_pos.2 (by omega)
  have hmul : 24 * ((s - 1) / 24) ≤ s - 1 := Nat.mul_div_le _ _
  have hsub_lt : s - 1 < s := Nat.sub_lt hspos (by omega)
  have hmul_lt : 24 * ((s - 1) / 24) < s := lt_of_le_of_lt hmul hsub_lt
  have hsquare : s * s ≤ 24 * ℓ := by
    dsimp [s]
    exact Nat.sqrt_le _
  change (24 * ((s - 1) / 24)) ^ 2 < 24 * ℓ
  simp only [pow_two]
  exact lt_of_lt_of_le (Nat.mul_self_lt_mul_self hmul_lt) hsquare

/-- The exact numerical inequality used in the paper.  The decimal constants
are exact rationals in Lean. -/
theorem numeric_cutoff (ℓ : ℕ) (hlarge : cutoff ≤ ℓ) :
    (81.12 : ℝ) * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 24 <
      Real.sqrt (24 * ℓ) := by
  let x : ℝ := ℓ
  let L : ℝ := 10 ^ 11
  have hxL : L ≤ x := by
    dsimp [L, x, cutoff] at *
    exact_mod_cast hlarge
  have hLpos : 0 < L := by norm_num [L]
  have hxpos : 0 < x := hLpos.trans_le hxL
  have hexp : Real.exp ((1 / 4 : ℝ)⁻¹) ≤ L := by
    norm_num only [one_div, inv_inv]
    exact (calc
      Real.exp (4 : ℝ) = Real.exp 1 ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < (2.7182818286 : ℝ) ^ (4 : ℕ) := by
        gcongr
        exact Real.exp_one_lt_d9
      _ ≤ (100000000000 : ℝ) := by norm_num).le
  have hratio_mono :
      Real.log x / x ^ (1 / 4 : ℝ) ≤
        Real.log L / L ^ (1 / 4 : ℝ) := by
    exact Real.log_div_self_rpow_antitoneOn
      (by norm_num : (0 : ℝ) < 1 / 4)
      hexp (hexp.trans hxL) hxL
  have hlogL : Real.log L < 26 := by
    dsimp [L]
    have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num]
      exact Real.log_mul (by norm_num) (by norm_num)
    rw [Real.log_pow, hlog10]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hrootL : (560 : ℝ) < L ^ (1 / 4 : ℝ) := by
    dsimp [L]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hratioL :
      Real.log L / L ^ (1 / 4 : ℝ) < (26 : ℝ) / 560 := by
    have hden : 0 < L ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hLpos _
    calc
      Real.log L / L ^ (1 / 4 : ℝ) <
          26 / L ^ (1 / 4 : ℝ) :=
        (div_lt_div_iff_of_pos_right hden).2 hlogL
      _ < 26 / 560 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) hrootL
  have hratio :
      Real.log x / x ^ (1 / 4 : ℝ) < (26 : ℝ) / 560 :=
    hratio_mono.trans_lt hratioL
  have hrpos : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hsqrt :
      Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
    norm_num
  have hfirst :
      (81.12 : ℝ) * x ^ (1 / 4 : ℝ) * Real.log x <
        4 * Real.sqrt x := by
    rw [hsqrt]
    have hid :
        (81.12 : ℝ) * x ^ (1 / 4 : ℝ) * Real.log x =
          81.12 * (Real.log x / x ^ (1 / 4 : ℝ)) *
            (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
      field_simp
    rw [hid]
    have hsquarepos :
        0 < x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := mul_pos hrpos hrpos
    have hc : (81.12 : ℝ) * ((26 : ℝ) / 560) < 4 := by norm_num
    nlinarith
  have hsqrtx : (300000 : ℝ) < Real.sqrt x := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hmiddle :
      (81.12 : ℝ) * x ^ (1 / 4 : ℝ) * Real.log x + 24 <
        4.8 * Real.sqrt x := by
    nlinarith
  have hsqrt24 : (4.8 : ℝ) < Real.sqrt 24 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hfinal : 4.8 * Real.sqrt x < Real.sqrt 24 * Real.sqrt x :=
    mul_lt_mul_of_pos_right hsqrt24 (Real.sqrt_pos.2 hxpos)
  dsimp [x] at hmiddle hfinal ⊢
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 24)]
  exact hmiddle.trans hfinal

/-- Combining the corrected `3.38` character bound with the numerical cutoff
gives the paper's discriminant inequality for `n = 24k - 1`. -/
theorem progression_index_lt_sqrt
    {ℓ k : ℕ} (hlarge : cutoff ≤ ℓ)
    (hk : (k : ℝ) ≤
      3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 1) :
    (24 * k : ℝ) < Real.sqrt (24 * ℓ) := by
  have hscaled :
      (24 : ℝ) * k ≤
        81.12 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 24 := by
    nlinarith
  exact hscaled.trans_lt (numeric_cutoff ℓ hlarge)

/-- Integer-cleared form of `progression_index_lt_sqrt`. -/
theorem progression_index_square_lt
    {ℓ k : ℕ} (hlarge : cutoff ≤ ℓ)
    (hk : (k : ℝ) ≤
      3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 1) :
    (24 * k) ^ 2 < 24 * ℓ := by
  have hreal := progression_index_lt_sqrt hlarge hk
  have hnonneg : (0 : ℝ) ≤ (24 * k : ℕ) := by positivity
  have hreal' :
      ((24 * k : ℕ) : ℝ) < Real.sqrt ((24 * ℓ : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact hreal
  have hsquare :
      ((24 * k : ℕ) : ℝ) ^ 2 < (24 * ℓ : ℕ) := by
    rwa [Real.lt_sqrt hnonneg] at hreal'
  exact_mod_cast hsquare

/-- Treviño's corrected estimate produces the bounded minimal inert member
of the progression.  Existence, positivity, the zero-free first value, and
the numerical cutoff are all proved internally. -/
theorem smallInertCandidate_of_trevino
    (Nonprincipal : ℕ → (ℤ → ℤ) → Prop)
    (hTrevino :
      PaperInterfaces.TrevinoCorrectedCharacterBound Nonprincipal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : cutoff ≤ ℓ)
    (hnonprincipal : Nonprincipal ℓ (legendreSym ℓ)) :
    ∃ n : ℕ,
      0 < n ∧ n % 24 = 23 ∧ ¬ IsSquare (-(n : ZMod ℓ)) ∧
      (n + 1) ^ 2 < 24 * ℓ ∧
      ∀ m : ℕ, 0 < m → m < n →
        ¬ (m % 24 = 23 ∧ ¬ IsSquare (-(m : ZMod ℓ))) := by
  let k := firstNonresidue ℓ
  have hex := firstNonresidue_exists hlarge
  have hkspec := firstNonresidue_spec hex
  have hkbound :=
    firstNonresidue_bound Nonprincipal hTrevino hlarge hnonprincipal
  have hksq := progression_index_square_lt hlarge hkbound
  let n := 24 * k - 1
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hnadd : n + 1 = 24 * k := by
    dsimp [n]
    omega
  have hnsq : (n + 1) ^ 2 < 24 * ℓ := by
    rw [hnadd]
    exact hksq
  have hnmod : n % 24 = 23 := by
    dsimp [n]
    omega
  have hnlt : n < ℓ :=
    n_lt_modulus_of_succ_sq_lt
      (by
        have : 24 < cutoff := by norm_num [cutoff]
        omega)
      hnsq
  have hncast : (n : ZMod ℓ) ≠ 0 := by
    intro hz
    have hdvd : ℓ ∣ n := (ZMod.natCast_eq_zero_iff n ℓ).mp hz
    have := Nat.le_of_dvd hnpos hdvd
    omega
  have hnum : (1 : ℤ) - 24 * (k : ℤ) = -(n : ℤ) := by
    dsimp [n]
    omega
  have hcharneg : legendreSym ℓ (-(n : ℤ)) = -1 := by
    rw [← hnum]
    apply (legendreSym.eq_neg_one_iff_not_one ℓ ?_).2 hkspec.2
    rw [hnum]
    push_cast
    exact neg_ne_zero.mpr hncast
  have hinert : ¬ IsSquare (-(n : ZMod ℓ)) := by
    have := (legendreSym.eq_neg_one_iff ℓ).1 hcharneg
    simpa using this
  refine ⟨n, hnpos, hnmod, hinert, hnsq, ?_⟩
  intro m hmpos hmlt hmprop
  rcases hmprop with ⟨hmmod, hminert⟩
  let j := (m + 1) / 24
  have hmadd : m + 1 = 24 * j := by
    dsimp [j]
    omega
  have hjpos : 0 < j := by omega
  have hjlt : j < k := by
    dsimp [n] at hmlt
    omega
  have hmchar : legendreSym ℓ (-(m : ℤ)) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using hminert
  have hinterval := character_interval_progression hex hjpos hjlt
  have harg : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ) := by
    exact_mod_cast
      (by omega : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ))
  rw [harg] at hinterval
  omega

/-- Uniform bounded-candidate input derived from Treviño, with no additional
arithmetic hypothesis. -/
theorem smallInertCandidateInput_of_trevino
    (Nonprincipal : ℕ → (ℤ → ℤ) → Prop)
    (hTrevino :
      PaperInterfaces.TrevinoCorrectedCharacterBound Nonprincipal)
    (hnonprincipal :
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], Nonprincipal ℓ (legendreSym ℓ)) :
    SmallInertCandidateInput := by
  intro ℓ hprime hlarge
  letI : Fact ℓ.Prime := ⟨hprime⟩
  exact smallInertCandidate_of_trevino
    Nonprincipal hTrevino hlarge (hnonprincipal ℓ)

/-! ### Reduced forms and the elementary class-number count -/

/-- Possible pairs `(a,b)` with `1 ≤ a ≤ M` and `|b| ≤ a`, encoded by
finite types.  The second coordinate represents `b+a`. -/
abbrev ReducedFormIndex (M : ℕ) :=
  Σ a : Fin M, Fin (2 * (a.val + 1) + 1)

/-- Decode the positive first coefficient. -/
def ReducedFormIndex.a {M : ℕ} (i : ReducedFormIndex M) : ℕ :=
  i.1.val + 1

/-- Decode the signed middle coefficient. -/
def ReducedFormIndex.b {M : ℕ} (i : ReducedFormIndex M) : ℤ :=
  (i.2.val : ℤ) - (i.a : ℤ)

/-- The usual reduced positive forms of discriminant `-n`, represented by
their bounded pair `(a,b)`; the coefficient `c` is uniquely determined by
the discriminant equation. -/
def IsReducedFormIndex (n : ℕ)
    (i : ReducedFormIndex (Nat.sqrt (n / 3))) : Prop :=
  ∃ c : ℕ,
    i.b ^ 2 - 4 * (i.a : ℤ) * c = -(n : ℤ) ∧
    i.a ≤ c ∧
    ((Int.natAbs i.b = i.a ∨ i.a = c) → 0 ≤ i.b)

/-- The elementary negative-discriminant class number used here is the
number of reduced positive forms.  For fundamental negative discriminants
this is the standard form-class definition of `h(-n)`. -/
noncomputable def negativeClassNumber (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {i : ReducedFormIndex (Nat.sqrt (n / 3)) //
    IsReducedFormIndex n i}

/-- Exact cardinality of the rectangular overcount of possible `(a,b)`. -/
theorem card_reducedFormIndex (M : ℕ) :
    Fintype.card (ReducedFormIndex M) = M ^ 2 + 2 * M := by
  simp only [ReducedFormIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 * (i + 1) + 1) M]
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      nlinarith

/-- Counting reduced forms by their first two coefficients gives the
paper's bound `h(-n) ≤ M²+2M`. -/
theorem negativeClassNumber_le (n : ℕ) :
    negativeClassNumber n ≤
      (Nat.sqrt (n / 3)) ^ 2 + 2 * Nat.sqrt (n / 3) := by
  classical
  unfold negativeClassNumber
  calc
    Fintype.card {i : ReducedFormIndex (Nat.sqrt (n / 3)) //
        IsReducedFormIndex n i} ≤
        Fintype.card (ReducedFormIndex (Nat.sqrt (n / 3))) :=
      Fintype.card_subtype_le _
    _ = (Nat.sqrt (n / 3)) ^ 2 + 2 * Nat.sqrt (n / 3) :=
      card_reducedFormIndex _

/-- Arithmetic core of the reduced-form class-number estimate.  The usual
reduction theory supplies `hcount`, while the elementary bounds on
`M = floor(sqrt(n/3))` are recorded without real square roots. -/
theorem class_number_bound_of_count
    {h n M : ℕ} (hnpos : 0 < n)
    (hcount : h ≤ M ^ 2 + 2 * M)
    (hM_sq : 3 * M ^ 2 ≤ n) (hM_linear : 6 * M < n) :
    h < n := by
  nlinarith

/-- The reduced-form count in the precise range needed by the paper.  The
single counting premise is the standard reduction-theory statement:
`M = floor √(n/3)` bounds the first coefficient and therefore the number of
classes by `M² + 2M`. -/
theorem class_number_bound_from_count
    {h n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hcount : ∃ M : ℕ, h ≤ M ^ 2 + 2 * M ∧ 3 * M ^ 2 ≤ n) :
    h < n := by
  have hn23 : 23 ≤ n := by omega
  obtain ⟨M, hcard, hM⟩ := hcount
  by_cases hMsmall : M ≤ 2
  · omega
  · have hMlarge : 3 ≤ M := by omega
    nlinarith

/-- For squarefree `n ≡ 23 (mod 24)`, the reduced-form class number satisfies
the exact paper bound `h(-n) < n`. -/
theorem class_number_bound
    {n : ℕ} (hsquarefree : Squarefree n) (hmod : n % 24 = 23) :
    negativeClassNumber n < n := by
  have hn23 : 23 ≤ n := by omega
  let M := Nat.sqrt (n / 3)
  have hMsq0 : M * M ≤ n / 3 := by
    dsimp [M]
    exact Nat.sqrt_le _
  have hdiv : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  have hMsq : 3 * M ^ 2 ≤ n := by
    simp only [pow_two]
    nlinarith
  apply class_number_bound_from_count hsquarefree hmod
  exact ⟨M, negativeClassNumber_le n, hMsq⟩

/-- The principal reduced form shows that the negative class number is
positive in the discriminant range used by the paper. -/
theorem negativeClassNumber_pos
    {n : ℕ} (hmod : n % 24 = 23) :
    0 < negativeClassNumber n := by
  classical
  have hn23 : 23 ≤ n := by omega
  let M := Nat.sqrt (n / 3)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.sqrt_pos.2 (by omega)
  let i : ReducedFormIndex M :=
    ⟨⟨0, hMpos⟩, ⟨2, by norm_num⟩⟩
  have hi : IsReducedFormIndex n i := by
    let c := (n + 1) / 4
    have hc : n + 1 = 4 * c := by
      dsimp [c]
      omega
    refine ⟨c, ?_, ?_, ?_⟩
    · dsimp [i, ReducedFormIndex.b, ReducedFormIndex.a]
      push_cast
      omega
    · dsimp [i, ReducedFormIndex.a, c]
      omega
    · intro _
      dsimp [i, ReducedFormIndex.b, ReducedFormIndex.a]
      norm_num
  unfold negativeClassNumber
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- Assembly of the last elementary estimates in the small-discriminant
lemma.  Squarefreeness/inertness come from the preceding minimality argument;
the cleared cutoff and class-number bound give the required degree bound. -/
theorem small_n_of_estimates
    (h : ℕ → ℕ) {ℓ n : ℕ}
    (hprime : ℓ.Prime) (hℓ : 96 < ℓ)
    (hsquarefree : Squarefree n) (hmod : n % 24 = 23)
    (hinert : ¬ IsSquare (-(n : ZMod ℓ)))
    (hsq : (n + 1) ^ 2 < 24 * ℓ)
    (hhpos : 0 < h n) (hhlt : h n < n) :
    Admissible ℓ n ∧ 0 < 2 * h n ∧ 2 * h n < ℓ := by
  refine ⟨⟨hsquarefree, hmod, hinert⟩, by omega, ?_⟩
  exact two_classNumber_lt_modulus hℓ hsq hhlt

/-- The standard reduced-form enumeration datum, separated from the analytic
character estimate. -/
def ReducedFormCountInput (h : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, Squarefree n → n % 24 = 23 →
    ∃ M : ℕ, h n ≤ M ^ 2 + 2 * M ∧ 3 * M ^ 2 ≤ n

/-- Paper-facing small-discriminant conclusion.  The cited analytic estimate
is represented by `SmallInertCandidateInput`; the remaining hypotheses are
the prime-square invariance and the standard reduced-form enumeration. -/
theorem small_n
    (Nonprincipal : ℕ → (ℤ → ℤ) → Prop)
    (hTrevino :
      PaperInterfaces.TrevinoCorrectedCharacterBound Nonprincipal)
    (hnonprincipal :
      ∀ (p : ℕ) [Fact p.Prime], Nonprincipal p (legendreSym p))
    (ℓ : ℕ) [Fact ℓ.Prime] (hlarge : cutoff ≤ ℓ) :
    ∃ n : ℕ,
      Squarefree n ∧ n % 24 = 23 ∧
      legendreSym ℓ (-(n : ℤ)) = -1 ∧
      ((n + 1 : ℕ) : ℝ) < Real.sqrt (24 * ℓ) ∧
      2 * negativeClassNumber n < ℓ := by
  have hprime : ℓ.Prime := Fact.out
  have hclass : ClassNumberEstimateInput negativeClassNumber := by
    intro n _ hsquarefree hmod
    exact ⟨negativeClassNumber_pos hmod,
      class_number_bound hsquarefree hmod⟩
  obtain ⟨n, hadm, hsq, _, hdegree⟩ :=
    smallDiscriminantInput_of_components negativeClassNumber
      (smallInertCandidateInput_of_trevino
        Nonprincipal hTrevino hnonprincipal)
      primeSquareInvarianceInput hclass
      ℓ hprime hlarge
  have hinert : legendreSym ℓ (-(n : ℤ)) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using hadm.2.2
  have hrealSq :
      (((n + 1 : ℕ) : ℝ)) ^ 2 < ((24 * ℓ : ℕ) : ℝ) := by
    exact_mod_cast hsq
  have hnnonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hroot :
      ((n + 1 : ℕ) : ℝ) < Real.sqrt (24 * ℓ) := by
    rw [Real.lt_sqrt hnnonneg]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    simpa using hrealSq
  exact ⟨n, hadm.1, hadm.2.1, hinert, hroot, hdegree⟩

end SptCM
