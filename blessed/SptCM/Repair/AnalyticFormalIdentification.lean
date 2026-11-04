module

public import blessed.SptCM.Repair.ActualLaurentBridge
public import blessed.SptCM.Repair.FormalHauptmodulEuler
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace SptCM.Repair

open scoped ModularForm Topology

/-- The standard nome of a point of the upper half plane lies in the open
unit disc.  This is the convergence input for every Euler product below. -/
theorem norm_qParam_lt_one (τ : UpperHalfPlane) :
    ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
  simpa [Function.Periodic.qParam, Complex.norm_exp] using
    (show Real.exp (-2 * Real.pi * τ.im) < 1 by
      rw [Real.exp_lt_one_iff]
      have h : 0 < (2 : ℝ) * Real.pi * τ.im :=
        mul_pos (mul_pos (by norm_num) Real.pi_pos) τ.im_pos
      linarith)

/-- Mathlib's `eta_q` factor is the corresponding positive power of the
standard nome. -/
theorem eta_q_eq_qParam_pow (n : ℕ) (z : ℂ) :
    ModularForm.eta_q n z = Function.Periodic.qParam 1 z ^ (n + 1) := by
  rfl

/-- Hence the Euler unit used in Mathlib is literally the convergent Euler
product in the standard nome, not a formal symbol. -/
theorem etaEulerUnit_eq_tprod_qParam (z : ℂ) :
    etaEulerUnit z =
      ∏' n : ℕ, (1 - Function.Periodic.qParam 1 z ^ (n + 1)) := by
  simp [etaEulerUnit, eta_q_eq_qParam_pow]

/-- Convergence of the actual Euler product follows from Mathlib's
Dedekind-eta convergence theorem. -/
theorem etaEulerUnit_multipliable (τ : UpperHalfPlane) :
    Multipliable
      (fun n : ℕ => 1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1)) :=
  ModularForm.multipliable_one_sub_pow (norm_qParam_lt_one τ)

/-- Scaling the upper-half-plane variable scales the standard nome by the
corresponding natural power. -/
theorem qParam_nat_mul (k : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((k : ℂ) * z) =
      Function.Periodic.qParam 1 z ^ k := by
  simp [Function.Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

/-- The analytic unit of the level-six Hauptmodul is therefore the concrete
quotient of four convergent Euler products at `q`, `q²`, `q³`, and `q⁶`. -/
theorem hauptmodulEulerUnit_eq_tprod_quotient (τ : UpperHalfPlane) :
    hauptmodulEulerUnit τ =
      (∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 5 *
        (∏' n : ℕ, (1 -
          (Function.Periodic.qParam 1 (τ : ℂ) ^ 3) ^ (n + 1))) /
          ((∏' n : ℕ, (1 -
            (Function.Periodic.qParam 1 (τ : ℂ) ^ 2) ^ (n + 1))) *
            (∏' n : ℕ, (1 -
              (Function.Periodic.qParam 1 (τ : ℂ) ^ 6) ^ (n + 1))) ^ 5) := by
  simp only [hauptmodulEulerUnit, etaEulerUnit_eq_tprod_qParam]
  have h2 : Function.Periodic.qParam 1 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ 2 := by
    simpa using qParam_nat_mul 2 (τ : ℂ)
  have h3 : Function.Periodic.qParam 1 (3 * (τ : ℂ)) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ 3 := by
    simpa using qParam_nat_mul 3 (τ : ℂ)
  have h6 : Function.Periodic.qParam 1 (6 * (τ : ℂ)) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ 6 := by
    simpa using qParam_nat_mul 6 (τ : ℂ)
  rw [h2, h3, h6]

/-- The coefficient stabilization built into `hauptmodulFormalEulerUnit` is
exposed as a theorem so the formal object can be compared to analytic finite
products without any principal-part assumption. -/
theorem hauptmodulFormalEulerUnit_coeff_stabilized (d : ℕ) :
    PowerSeries.coeff d hauptmodulFormalEulerUnit =
      PowerSeries.coeff d
        (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1)) := by
  simp [hauptmodulFormalEulerUnit]

/-- A precise record of the two non-negotiable parts of the analytic/formal
identification: analytic convergence of Mathlib's Euler product and
coefficientwise stabilization of the integral formal product. -/
structure AnalyticFormalEulerIdentification (τ : UpperHalfPlane) : Prop where
  nomeInUnitDisk : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1
  etaProductConverges : Multipliable
    (fun n : ℕ => 1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))
  etaProductValue : etaEulerUnit τ =
    ∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))
  formalCoefficientsStabilize : ∀ d : ℕ,
    PowerSeries.coeff d hauptmodulFormalEulerUnit =
      PowerSeries.coeff d
        (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1))

/-- The actual Dedekind eta Euler product and the independently constructed
integral stabilized series satisfy the analytic convergence and formal
stabilization halves of the identification. -/
theorem analyticFormalEulerIdentification (τ : UpperHalfPlane) :
    AnalyticFormalEulerIdentification τ := by
  exact ⟨norm_qParam_lt_one τ, etaEulerUnit_multipliable τ,
    etaEulerUnit_eq_tprod_qParam τ, hauptmodulFormalEulerUnit_coeff_stabilized⟩


/-- The `N`th finite Euler product. -/
@[expose]
noncomputable def etaEulerPartial (q : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))

/-- The convergent Euler product has no zero in the open unit disk.  This is
needed to pass to the quotient defining the Hauptmodul unit. -/
theorem tprod_one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -q ^ (n + 1))
  · intro n
    change 1 - q ^ (n + 1) ≠ 0
    rw [sub_ne_zero]
    intro h
    have hn : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    rw [← h, norm_one] at hn
    exact (lt_irrefl 1 hn)
  · simpa only [norm_neg, norm_pow] using
      (summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (norm_nonneg q) hq)

/-- The finite Euler products tend to Mathlib's `tprod`. -/
theorem etaEulerPartial_tendsto {q : ℂ} (hq : ‖q‖ < 1) :
    Filter.Tendsto (etaEulerPartial q) Filter.atTop
      (nhds (∏' n : ℕ, (1 - q ^ (n + 1)))) := by
  unfold etaEulerPartial
  exact (ModularForm.multipliable_one_sub_pow hq).tendsto_prod_tprod_nat

/-- The simultaneous finite approximation to the level-six Euler unit. -/
@[expose]
noncomputable def hauptmodulEulerPartial (q : ℂ) (N : ℕ) : ℂ :=
  etaEulerPartial q N ^ 5 * etaEulerPartial (q ^ 3) N /
    (etaEulerPartial (q ^ 2) N * etaEulerPartial (q ^ 6) N ^ 5)

/-- The concrete finite products converge to the analytic Hauptmodul Euler
unit.  In particular all division in the limit is justified by nonvanishing,
rather than being treated formally. -/
theorem hauptmodulEulerPartial_tendsto (τ : UpperHalfPlane) :
    Filter.Tendsto
      (hauptmodulEulerPartial (Function.Periodic.qParam 1 (τ : ℂ))) Filter.atTop
      (nhds (hauptmodulEulerUnit τ)) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := norm_qParam_lt_one τ
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hq6 : ‖q ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h1 := etaEulerPartial_tendsto hq
  have h2 := etaEulerPartial_tendsto hq2
  have h3 := etaEulerPartial_tendsto hq3
  have h6 := etaEulerPartial_tendsto hq6
  have hden :
      (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
        (∏' n : ℕ, (1 - (q ^ 6) ^ (n + 1))) ^ 5 ≠ 0 := by
    exact mul_ne_zero (tprod_one_sub_pow_ne_zero hq2)
      (pow_ne_zero _ (tprod_one_sub_pow_ne_zero hq6))
  rw [hauptmodulEulerUnit_eq_tprod_quotient]
  exact ((h1.pow 5).mul h3).div (h2.mul (h6.pow 5)) hden


/-- The Euler product as a holomorphic function of the nome. -/
@[expose]
noncomputable def etaEulerDisk (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

/-- The level-six unit as a function on the nome disk. -/
@[expose]
noncomputable def hauptmodulEulerDisk (q : ℂ) : ℂ :=
  etaEulerDisk q ^ 5 * etaEulerDisk (q ^ 3) /
    (etaEulerDisk (q ^ 2) * etaEulerDisk (q ^ 6) ^ 5)

/-- Mathlib's local uniform convergence theorem gives local uniform
convergence of the ordinary initial partial products, the precise analytic
limit needed for coefficient extraction. -/
theorem etaEulerPartial_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun N q => etaEulerPartial q N) etaEulerDisk Filter.atTop
      (Metric.ball (0 : ℂ) 1) := by
  unfold etaEulerPartial etaEulerDisk
  exact ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
    |>.tendstoLocallyUniformlyOn_finsetRange

/-- The simultaneous finite Hauptmodul products converge locally uniformly on the
unit disk.  This strengthens pointwise convergence enough to pass to every Taylor
coefficient. -/
theorem hauptmodulEulerPartial_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun N q => hauptmodulEulerPartial q N) hauptmodulEulerDisk Filter.atTop
      (Metric.ball (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball (0 : ℂ) 1
  have hmap (k : ℕ) (hk : k ≠ 0) : Set.MapsTo (fun q : ℂ => q ^ k) U U := by
    intro q hq
    simp only [U, Metric.mem_ball, dist_zero_right, norm_pow] at hq ⊢
    exact pow_lt_one₀ (norm_nonneg q) hq hk
  have hcomp (k : ℕ) (hk : k ≠ 0) :
      TendstoLocallyUniformlyOn
        (fun N q => etaEulerPartial (q ^ k) N) (fun q => etaEulerDisk (q ^ k))
        Filter.atTop U := by
    simpa only [Function.comp_def] using
      etaEulerPartial_tendstoLocallyUniformlyOn.comp (fun q : ℂ => q ^ k)
        (hmap k hk) (by fun_prop)
  have heta : ContinuousOn etaEulerDisk U := by
    exact ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn
  have hc (k : ℕ) (hk : k ≠ 0) :
      ContinuousOn (fun q : ℂ => etaEulerDisk (q ^ k)) U := by
    exact heta.comp (by fun_prop) (hmap k hk)
  have h1 := etaEulerPartial_tendstoLocallyUniformlyOn
  have h2 := hcomp 2 (by norm_num)
  have h3 := hcomp 3 (by norm_num)
  have h6 := hcomp 6 (by norm_num)
  have hc1 : ContinuousOn etaEulerDisk U := heta
  have hc2 := hc 2 (by norm_num)
  have hc3 := hc 3 (by norm_num)
  have hc6 := hc 6 (by norm_num)
  have h1sq := h1.mul₀ h1 hc1 hc1
  have hc1sq : ContinuousOn (fun q => etaEulerDisk q * etaEulerDisk q) U := hc1.mul hc1
  have h1four := h1sq.mul₀ h1sq hc1sq hc1sq
  have hc1four : ContinuousOn
      (fun q => (etaEulerDisk q * etaEulerDisk q) *
        (etaEulerDisk q * etaEulerDisk q)) U := hc1sq.mul hc1sq
  have h1five := h1four.mul₀ h1 hc1four hc1
  have hc1five : ContinuousOn
      (fun q => ((etaEulerDisk q * etaEulerDisk q) *
        (etaEulerDisk q * etaEulerDisk q)) * etaEulerDisk q) U := hc1four.mul hc1
  have h6sq := h6.mul₀ h6 hc6 hc6
  have hc6sq : ContinuousOn
      (fun q => etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6)) U := hc6.mul hc6
  have h6four := h6sq.mul₀ h6sq hc6sq hc6sq
  have hc6four : ContinuousOn
      (fun q => (etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6)) *
        (etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6))) U := hc6sq.mul hc6sq
  have h6five := h6four.mul₀ h6 hc6four hc6
  have hc6five : ContinuousOn
      (fun q => ((etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6)) *
        (etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6))) * etaEulerDisk (q ^ 6)) U :=
    hc6four.mul hc6
  have hnum := h1five.mul₀ h3 hc1five hc3
  have hcnum : ContinuousOn
      (fun q => (((etaEulerDisk q * etaEulerDisk q) *
        (etaEulerDisk q * etaEulerDisk q)) * etaEulerDisk q) *
          etaEulerDisk (q ^ 3)) U := hc1five.mul hc3
  have hden := h2.mul₀ h6five hc2 hc6five
  have hcden : ContinuousOn
      (fun q => etaEulerDisk (q ^ 2) *
        (((etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6)) *
          (etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6))) * etaEulerDisk (q ^ 6))) U :=
    hc2.mul hc6five
  have hden0 : ∀ q ∈ U,
      etaEulerDisk (q ^ 2) *
        (((etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6)) *
          (etaEulerDisk (q ^ 6) * etaEulerDisk (q ^ 6))) * etaEulerDisk (q ^ 6)) ≠ 0 := by
    intro q hq
    have hqn : ‖q‖ < 1 := by simpa [U, Metric.mem_ball, dist_zero_right] using hq
    have hq2 : ‖q ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqn (by norm_num)
    have hq6 : ‖q ^ 6‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqn (by norm_num)
    have hz2 := tprod_one_sub_pow_ne_zero hq2
    have hz6 := tprod_one_sub_pow_ne_zero hq6
    simpa [etaEulerDisk, pow_succ, mul_assoc] using
      (mul_ne_zero hz2 (pow_ne_zero 5 hz6))
  have hquot := hnum.div₀ hden hcnum hcden hden0
  convert hquot using 1
  · funext N q
    simp [hauptmodulEulerPartial, Pi.mul_apply, Pi.div_apply,
      div_eq_mul_inv, pow_succ, mul_assoc]
  · funext q
    simp [hauptmodulEulerDisk, Pi.mul_apply, Pi.div_apply,
      div_eq_mul_inv, pow_succ, mul_assoc]

/-- Every finite simultaneous Euler quotient is holomorphic on the unit disk. -/
theorem hauptmodulEulerPartial_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (fun q => hauptmodulEulerPartial q N)
      (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hqn : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  have hpow (k : ℕ) (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqn hk
  have hcomp (k : ℕ) :
      DifferentiableAt ℂ (fun z : ℂ => etaEulerPartial (z ^ k) N) q := by
    unfold etaEulerPartial
    fun_prop
  have hnz (k : ℕ) (hk : k ≠ 0) : etaEulerPartial (q ^ k) N ≠ 0 := by
    unfold etaEulerPartial
    rw [Finset.prod_ne_zero_iff]
    intro n hn
    rw [sub_ne_zero]
    intro heq
    have hlt : ‖(q ^ k) ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg (q ^ k)) (hpow k hk) (Nat.succ_ne_zero n)
    rw [← heq, norm_one] at hlt
    exact (lt_irrefl 1 hlt)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => etaEulerPartial z N) q := by
    simpa using hcomp 1
  have h2 := hcomp 2
  have h3 := hcomp 3
  have h6 := hcomp 6
  have hden : etaEulerPartial (q ^ 2) N * etaEulerPartial (q ^ 6) N ^ 5 ≠ 0 :=
    mul_ne_zero (hnz 2 (by norm_num)) (pow_ne_zero _ (hnz 6 (by norm_num)))
  unfold hauptmodulEulerPartial
  exact (((h1.pow 5).mul h3).div (h2.mul (h6.pow 5)) hden).differentiableWithinAt

/-- Local uniform convergence persists after taking any fixed number of
complex derivatives. -/
theorem hauptmodulEulerPartial_iteratedDeriv_tendstoLocallyUniformlyOn (d : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N => iteratedDeriv d (fun q => hauptmodulEulerPartial q N))
      (iteratedDeriv d hauptmodulEulerDisk) Filter.atTop
      (Metric.ball (0 : ℂ) 1) := by
  have hdiff (N : ℕ) (j : ℕ) :
      DifferentiableOn ℂ (iteratedDeriv j (fun q => hauptmodulEulerPartial q N))
        (Metric.ball (0 : ℂ) 1) := by
    rw [iteratedDeriv_eq_iterate]
    exact ((hauptmodulEulerPartial_differentiableOn N).analyticOnNhd Metric.isOpen_ball
      |>.iterated_deriv j).differentiableOn
  induction d with
  | zero =>
      simpa using hauptmodulEulerPartial_tendstoLocallyUniformlyOn
  | succ d ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (.of_forall fun N => hdiff N d) Metric.isOpen_ball

/-- In particular, every finite-product Taylor coefficient converges to the
corresponding coefficient of the analytic Hauptmodul disk function. -/
theorem hauptmodulEulerPartial_taylorCoeff_tendsto (d : ℕ) :
    Filter.Tendsto
      (fun N => (d.factorial : ℂ)⁻¹ *
        iteratedDeriv d (fun q => hauptmodulEulerPartial q N) 0)
      Filter.atTop
      (nhds ((d.factorial : ℂ)⁻¹ * iteratedDeriv d hauptmodulEulerDisk 0)) := by
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  exact (((hauptmodulEulerPartial_iteratedDeriv_tendstoLocallyUniformlyOn d).tendsto_at
    hzero).const_mul (d.factorial : ℂ)⁻¹)

/-- The Euler disk function is holomorphic, as a locally uniform limit of
its polynomial partial products. -/
theorem etaEulerDisk_differentiableOn :
    DifferentiableOn ℂ etaEulerDisk (Metric.ball (0 : ℂ) 1) := by
  unfold etaEulerDisk
  exact ModularForm.differentiableOn_tprod_one_sub_pow

/-- At an upper-half-plane nome, the disk model is exactly the analytic Euler
unit appearing in the eta quotient. -/
theorem hauptmodulEulerDisk_qParam (τ : UpperHalfPlane) :
    hauptmodulEulerDisk (Function.Periodic.qParam 1 (τ : ℂ)) =
      hauptmodulEulerUnit τ := by
  rw [hauptmodulEulerUnit_eq_tprod_quotient]
  rfl


/-- The analytic Euler product is equal throughout the unit disk to its
Taylor series.  The sole remaining identification is therefore the algebraic
calculation of these Taylor coefficients. -/
theorem etaEulerDisk_taylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (n.factorial : ℂ)⁻¹ *
      iteratedDeriv n etaEulerDisk 0 * q ^ n) = etaEulerDisk q := by
  simpa using Complex.taylorSeries_eq_on_ball'
    (c := 0) (r := 1) (z := q)
    (by simpa [Metric.mem_ball, dist_zero_right] using hq)
    etaEulerDisk_differentiableOn

/-- The level-six quotient is holomorphic on the unit disk; nonvanishing of
the denominator is supplied by the convergent-product theorem above. -/
theorem hauptmodulEulerDisk_differentiableOn :
    DifferentiableOn ℂ hauptmodulEulerDisk (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hqn : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  have hpow (k : ℕ) (hk : k ≠ 0) : q ^ k ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqn hk
  have hcomp (k : ℕ) (hk : k ≠ 0) :
      DifferentiableAt ℂ (fun z : ℂ => etaEulerDisk (z ^ k)) q := by
    exact ((etaEulerDisk_differentiableOn (q ^ k) (hpow k hk)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hpow k hk))).comp q (differentiableAt_id.pow k)
  have hself : DifferentiableAt ℂ etaEulerDisk q :=
    (etaEulerDisk_differentiableOn q hq).differentiableAt
      (Metric.isOpen_ball.mem_nhds hq)
  have h2 := hcomp 2 (by norm_num)
  have h3 := hcomp 3 (by norm_num)
  have h6 := hcomp 6 (by norm_num)
  have hden : etaEulerDisk (q ^ 2) * etaEulerDisk (q ^ 6) ^ 5 ≠ 0 := by
    unfold etaEulerDisk
    exact mul_ne_zero
      (tprod_one_sub_pow_ne_zero (by simpa [Metric.mem_ball, dist_zero_right] using hpow 2 (by norm_num)))
      (pow_ne_zero _
        (tprod_one_sub_pow_ne_zero (by simpa [Metric.mem_ball, dist_zero_right] using hpow 6 (by norm_num))))
  exact (((hself.pow 5).mul h3).div (h2.mul (h6.pow 5)) hden).differentiableWithinAt

/-- Consequently the analytic level-six Euler unit is itself equal to its
Taylor series on the whole unit disk. -/
theorem hauptmodulEulerDisk_taylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (n.factorial : ℂ)⁻¹ *
      iteratedDeriv n hauptmodulEulerDisk 0 * q ^ n) =
        hauptmodulEulerDisk q := by
  simpa using Complex.taylorSeries_eq_on_ball'
    (c := 0) (r := 1) (z := q)
    (by simpa [Metric.mem_ball, dist_zero_right] using hq)
    hauptmodulEulerDisk_differentiableOn


/-- The formal Taylor series at zero, packaged as an ordinary algebraic power
series.  This lets us compare the analytic finite Euler quotients with the
integral formal products coefficient by coefficient. -/
@[expose]
noncomputable def analyticTaylorPowerSeries (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

@[simp] theorem analyticTaylorPowerSeries_coeff (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (analyticTaylorPowerSeries f) =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 := by
  simp [analyticTaylorPowerSeries]

/-- Taylor series multiplication, with all factorial normalization made
explicit. -/
theorem analyticTaylorPowerSeries_mul (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticTaylorPowerSeries (fun z => f z * g z) =
      analyticTaylorPowerSeries f * analyticTaylorPowerSeries g := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [analyticTaylorPowerSeries_coeff]
  rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le le_top)
    (hg.contDiffAt.of_le le_top)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) *
      ((n-i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n-i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n-i)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hi0, hni0, hn0]
  calc
    _ = ((n.choose i : ℂ) * (i.factorial : ℂ) * ((n-i).factorial : ℂ)) *
        (iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0) := by ring
    _ = _ := by rw [hfac]; ring

 theorem analyticTaylorPowerSeries_sub (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticTaylorPowerSeries (fun z => f z - g z) =
      analyticTaylorPowerSeries f - analyticTaylorPowerSeries g := by
  ext n
  simp only [analyticTaylorPowerSeries_coeff, map_sub]
  rw [iteratedDeriv_fun_sub (hf.contDiffAt.of_le le_top)
    (hg.contDiffAt.of_le le_top)]
  ring

@[simp] theorem analyticTaylorPowerSeries_one :
    analyticTaylorPowerSeries (fun _ : ℂ => 1) = 1 := by
  ext n
  simp [analyticTaylorPowerSeries, iteratedDeriv_const]
  split_ifs <;> simp_all

@[simp] theorem analyticTaylorPowerSeries_powfun (m : ℕ) :
    analyticTaylorPowerSeries (fun z : ℂ => z ^ m) = PowerSeries.X ^ m := by
  ext n
  rw [analyticTaylorPowerSeries_coeff, PowerSeries.coeff_X_pow,
    iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst n
    apply inv_mul_cancel₀
    exact_mod_cast Nat.factorial_ne_zero m
  · simp

 theorem analyticTaylorPowerSeries_one_sub_pow (m : ℕ) :
    analyticTaylorPowerSeries (fun z : ℂ => 1 - z ^ m) =
      1 - PowerSeries.X ^ m := by
  simpa using analyticTaylorPowerSeries_sub (fun _ : ℂ => 1) (fun z => z ^ m)
    analyticAt_const (analyticAt_id.pow m)

 theorem analyticTaylorPowerSeries_pow (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    analyticTaylorPowerSeries (fun z => f z ^ k) =
      analyticTaylorPowerSeries f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      change analyticTaylorPowerSeries (fun z => f z ^ k * f z) = _
      rw [pow_succ]
      have hm := analyticTaylorPowerSeries_mul (fun z => f z ^ k) f (hf.pow k) hf
      simpa only using hm.trans (congrArg (fun P => P * analyticTaylorPowerSeries f) ih)


/-- Analytic germs which agree near zero have the same formal Taylor power
series. -/
theorem analyticTaylorPowerSeries_eq_of_eventuallyEq (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : f =ᶠ[nhds 0] g) :
    analyticTaylorPowerSeries f = analyticTaylorPowerSeries g := by
  have hseries := hf.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hg.hasFPowerSeriesAt hfg
  ext n
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hseries
  simpa [analyticTaylorPowerSeries, FormalMultilinearSeries.coeff_ofScalars,
    div_eq_inv_mul] using hc

/-- Formal substitution of `X^k` into the standard inverse power series is
indeed inverse to `(1-X^k)^a`. -/
theorem subst_invOneSubPow_mul (k a : ℕ) (hk : k ≠ 0) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ k)
      (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ) *
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) ^ a = 1 := by
  have hs := PowerSeries.HasSubst.X_pow (R := ℂ) hk
  have hd : PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ k)
      ((1 - PowerSeries.X) ^ a : PowerSeries ℂ) =
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) ^ a := by
    rw [PowerSeries.subst_pow hs, PowerSeries.subst_sub hs,
      PowerSeries.subst_X hs]
    change (PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ k)
      (PowerSeries.C 1) - _) ^ a = _
    rw [PowerSeries.subst_C, map_one]
  rw [← hd, ← PowerSeries.subst_mul hs]
  rw [show (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ) *
      (1 - PowerSeries.X) ^ a = 1 by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact_mod_cast Units.mul_inv (PowerSeries.invOneSubPow ℂ a)]
  change PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ k)
    (PowerSeries.C 1) = 1
  rw [PowerSeries.subst_C, map_one]

/-- The analytic reciprocal factor has precisely the substituted formal
binomial series as its Taylor expansion. -/
theorem analyticTaylorPowerSeries_inv_one_sub_pow (k a : ℕ) (hk : k ≠ 0) :
    analyticTaylorPowerSeries (fun z : ℂ => 1 / (1 - z ^ k) ^ a) =
      PowerSeries.subst (PowerSeries.X ^ k)
        (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ) := by
  let r : ℂ → ℂ := fun z => 1 / (1 - z ^ k) ^ a
  let d : ℂ → ℂ := fun z => (1 - z ^ k) ^ a
  have hd : AnalyticAt ℂ d 0 := (analyticAt_const.sub (analyticAt_id.pow k)).pow a
  have hd0 : d 0 ≠ 0 := by simp [d, hk]
  have hr : AnalyticAt ℂ r 0 := by
    dsimp [r]
    exact analyticAt_const.div hd hd0
  have heq : (fun z => r z * d z) =ᶠ[nhds 0] (fun _ : ℂ => 1) := by
    have hne : ∀ᶠ z in nhds (0 : ℂ), d z ≠ 0 := hd.continuousAt.eventually_ne hd0
    filter_upwards [hne] with z hz
    dsimp [r]
    change (1 - z ^ k) ^ a ≠ 0 at hz
    exact div_mul_cancel₀ 1 hz
  have htd : analyticTaylorPowerSeries d =
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) ^ a := by
    dsimp [d]
    have hp := analyticTaylorPowerSeries_pow (fun z : ℂ => 1 - z ^ k)
      (analyticAt_const.sub (analyticAt_id.pow k)) a
    rw [analyticTaylorPowerSeries_one_sub_pow] at hp
    exact hp
  have han : analyticTaylorPowerSeries r *
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) ^ a = 1 := by
    rw [← htd]
    have hm := analyticTaylorPowerSeries_mul r d hr hd
    rw [← hm]
    have hprod : AnalyticAt ℂ (fun z => r z * d z) 0 := by
      dsimp [r, d]
      fun_prop
    rw [analyticTaylorPowerSeries_eq_of_eventuallyEq _ _ hprod
      analyticAt_const heq]
    exact analyticTaylorPowerSeries_one
  have hform := subst_invOneSubPow_mul k a hk
  have hbase : 1 - (PowerSeries.X : PowerSeries ℂ) ^ k ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 0) h
    simp [hk] at hc
  have hden : (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) ^ a ≠ 0 :=
    pow_ne_zero a hbase
  apply mul_right_cancel₀ hden
  exact han.trans hform.symm


/-- One analytic Euler factor, arranged multiplicatively so that it matches
`hauptmodulFormalEulerFactor` term for term. -/
@[expose]
noncomputable def hauptmodulEulerAnalyticFactor (q : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m) ^ 5 * (1 - q ^ (3 * m)) *
    (1 / (1 - q ^ (2 * m))) * (1 / (1 - q ^ (6 * m)) ^ 5)

/-- Taylor expansion of a single analytic factor is the corresponding
complex formal Euler factor. -/
theorem analyticTaylorPowerSeries_hauptmodulEulerAnalyticFactor
    (m : ℕ) (hm : m ≠ 0) :
    analyticTaylorPowerSeries (fun q => hauptmodulEulerAnalyticFactor q m) =
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ m) ^ 5 *
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ (3 * m)) *
      PowerSeries.subst (PowerSeries.X ^ (2 * m))
        (PowerSeries.invOneSubPow ℂ 1 : PowerSeries ℂ) *
      PowerSeries.subst (PowerSeries.X ^ (6 * m))
        (PowerSeries.invOneSubPow ℂ 5 : PowerSeries ℂ) := by
  let A : ℂ → ℂ := fun q => (1 - q ^ m) ^ 5
  let B : ℂ → ℂ := fun q => 1 - q ^ (3 * m)
  let C : ℂ → ℂ := fun q => 1 / (1 - q ^ (2 * m))
  let D : ℂ → ℂ := fun q => 1 / (1 - q ^ (6 * m)) ^ 5
  have hA : AnalyticAt ℂ A 0 := by dsimp [A]; fun_prop
  have hB : AnalyticAt ℂ B 0 := by dsimp [B]; fun_prop
  have hC : AnalyticAt ℂ C 0 := by
    dsimp [C]
    exact analyticAt_const.div (analyticAt_const.sub (analyticAt_id.pow (2 * m)))
      (by simp [hm])
  have hD : AnalyticAt ℂ D 0 := by
    dsimp [D]
    exact analyticAt_const.div
      ((analyticAt_const.sub (analyticAt_id.pow (6 * m))).pow 5) (by simp [hm])
  have hmul1 := analyticTaylorPowerSeries_mul A B hA hB
  have hAB : AnalyticAt ℂ (fun q => A q * B q) 0 := by
    dsimp [A, B]
    fun_prop
  have hABC : AnalyticAt ℂ (fun q => A q * B q * C q) 0 := by
    exact hAB.fun_mul hC
  have hmul2 := analyticTaylorPowerSeries_mul (fun q => A q * B q) C hAB hC
  have hmul3 := analyticTaylorPowerSeries_mul (fun q => A q * B q * C q) D hABC hD
  dsimp [hauptmodulEulerAnalyticFactor, A, B, C, D] at hmul1 hmul2 hmul3 ⊢
  rw [hmul3, hmul2, hmul1]
  have hta := analyticTaylorPowerSeries_pow (fun q : ℂ => 1 - q ^ m)
    (analyticAt_const.sub (analyticAt_id.pow m)) 5
  rw [analyticTaylorPowerSeries_one_sub_pow] at hta
  rw [hta, analyticTaylorPowerSeries_one_sub_pow]
  have htC := analyticTaylorPowerSeries_inv_one_sub_pow (2 * m) 1
    (mul_ne_zero (by norm_num) hm)
  have htC' : analyticTaylorPowerSeries (fun q : ℂ => 1 / (1 - q ^ (2*m))) =
      PowerSeries.subst (PowerSeries.X ^ (2*m))
        (PowerSeries.invOneSubPow ℂ 1 : PowerSeries ℂ) := by simpa using htC
  rw [htC']
  rw [analyticTaylorPowerSeries_inv_one_sub_pow (6 * m) 5
    (mul_ne_zero (by norm_num) hm)]

/-- The simultaneous finite quotient is the product of the individual
analytic Euler factors. -/
theorem hauptmodulEulerPartial_eq_prod_factor (q : ℂ) (N : ℕ) :
    hauptmodulEulerPartial q N =
      ∏ i ∈ Finset.range N, hauptmodulEulerAnalyticFactor q (i + 1) := by
  simp only [hauptmodulEulerPartial, etaEulerPartial,
    hauptmodulEulerAnalyticFactor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  simp only [← Finset.prod_pow, one_div]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- Casting the standard formal inverse binomial series from `ℤ` to `ℂ`
commutes with its coefficients. -/
theorem map_invOneSubPow_int_complex (a : ℕ) :
    PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.invOneSubPow ℤ a : PowerSeries ℤ) =
      (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ) := by
  ext n
  cases a with
  | zero => simp [PowerSeries.invOneSubPow]
  | succ a =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    simp

/-- The complex formal factor is coefficientwise the cast of the integral
formal factor. -/
theorem map_hauptmodulFormalEulerFactor (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.map (Int.castRingHom ℂ) (hauptmodulFormalEulerFactor m) =
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ m) ^ 5 *
      (1 - (PowerSeries.X : PowerSeries ℂ) ^ (3 * m)) *
      PowerSeries.subst (PowerSeries.X ^ (2 * m))
        (PowerSeries.invOneSubPow ℂ 1 : PowerSeries ℂ) *
      PowerSeries.subst (PowerSeries.X ^ (6 * m))
        (PowerSeries.invOneSubPow ℂ 5 : PowerSeries ℂ) := by
  have hmapSubst (c a : ℕ) (hc : c ≠ 0) :
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.subst ((PowerSeries.X : PowerSeries ℤ) ^ c)
          (PowerSeries.invOneSubPow ℤ a : PowerSeries ℤ)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ c)
        (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ) := by
    ext n
    rw [PowerSeries.coeff_map,
      PowerSeries.coeff_subst_X_pow (R := ℤ) (S := ℤ) hc,
      PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) hc]
    split_ifs with h
    · change (Int.castRingHom ℂ) (PowerSeries.coeff (n / c)
          (PowerSeries.invOneSubPow ℤ a : PowerSeries ℤ)) =
          PowerSeries.coeff (n / c)
            (PowerSeries.invOneSubPow ℂ a : PowerSeries ℂ)
      have hh := congrArg (PowerSeries.coeff (n / c))
        (map_invOneSubPow_int_complex a)
      simpa using hh
    · simp
  have hmap2 := hmapSubst (2 * m) 1 (mul_ne_zero (by norm_num) hm)
  have hmap6 := hmapSubst (6 * m) 5 (mul_ne_zero (by norm_num) hm)
  simp only [hauptmodulFormalEulerFactor, map_mul, map_pow, map_sub,
    map_one, PowerSeries.map_X, hmap2, hmap6]


/-- `LowCoefficientsOne P m` says that `P` is congruent to `1` through
all degrees strictly below `m`. -/
@[expose]
def LowCoefficientsOne {R : Type*} [CommRing R]
    (P : PowerSeries R) (m : ℕ) : Prop :=
  ∀ n < m, PowerSeries.coeff n P = PowerSeries.coeff n 1

private theorem coeff_mul_of_lowCoefficientsOne_right
    {R : Type*} [CommRing R] (P Q : PowerSeries R) (n : ℕ)
    (hQ : ∀ j ≤ n, PowerSeries.coeff j Q = PowerSeries.coeff j 1) :
    PowerSeries.coeff n (P * Q) = PowerSeries.coeff n P := by
  rw [PowerSeries.coeff_mul]
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff ij.1 P * PowerSeries.coeff ij.2 1 := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hQ ij.2 (by
        have hs : ij.1 + ij.2 = n := by simpa using hij
        omega)]
    _ = PowerSeries.coeff n (P * 1) := by rw [PowerSeries.coeff_mul]
    _ = PowerSeries.coeff n P := by simp

private theorem LowCoefficientsOne.mul
    {R : Type*} [CommRing R] {P Q : PowerSeries R} {m : ℕ}
    (hP : LowCoefficientsOne P m) (hQ : LowCoefficientsOne Q m) :
    LowCoefficientsOne (P * Q) m := by
  intro n hn
  rw [coeff_mul_of_lowCoefficientsOne_right P Q n
    (fun j hj => hQ j (lt_of_le_of_lt hj hn))]
  exact hP n hn

private theorem LowCoefficientsOne.pow
    {R : Type*} [CommRing R] {P : PowerSeries R} {m : ℕ}
    (hP : LowCoefficientsOne P m) (a : ℕ) :
    LowCoefficientsOne (P ^ a) m := by
  induction a with
  | zero => simp [LowCoefficientsOne]
  | succ a ih => rw [pow_succ]; exact ih.mul hP

private theorem lowCoefficientsOne_one_sub_X_pow
    {R : Type*} [CommRing R] (k m : ℕ) (hmk : m ≤ k) :
    LowCoefficientsOne (1 - (PowerSeries.X : PowerSeries R) ^ k) m := by
  intro n hn
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  have hne : n ≠ k := by omega
  simp [hne]

private theorem lowCoefficientsOne_subst_invOneSubPow
    {R : Type*} [CommRing R] (k a m : ℕ) (hk : k ≠ 0) (hmk : m ≤ k) :
    LowCoefficientsOne
      (PowerSeries.subst ((PowerSeries.X : PowerSeries R) ^ k)
        (PowerSeries.invOneSubPow R a : PowerSeries R)) m := by
  intro n hn
  rw [PowerSeries.coeff_subst_X_pow (R := R) (S := R) hk]
  by_cases hn0 : n = 0
  · subst n
    cases a <;> simp [PowerSeries.invOneSubPow]
  · have hnd : ¬k ∣ n := by
      intro hd
      have hle := Nat.le_of_dvd (by omega : 0 < n) hd
      omega
    simp [hnd, hn0]

/-- The `m`th integral formal Euler factor is `1` modulo `X^m`. -/
theorem hauptmodulFormalEulerFactor_lowCoefficientsOne
    (m : ℕ) (hm : m ≠ 0) :
    LowCoefficientsOne (hauptmodulFormalEulerFactor m) m := by
  unfold hauptmodulFormalEulerFactor
  have h1 := (lowCoefficientsOne_one_sub_X_pow (R := ℤ) m m le_rfl).pow 5
  have h3 := lowCoefficientsOne_one_sub_X_pow (R := ℤ) (3*m) m (by omega)
  have h2 := lowCoefficientsOne_subst_invOneSubPow (R := ℤ)
    (2*m) 1 m (mul_ne_zero (by norm_num) hm) (by omega)
  have h6 := lowCoefficientsOne_subst_invOneSubPow (R := ℤ)
    (6*m) 5 m (mul_ne_zero (by norm_num) hm) (by omega)
  exact ((h1.mul h3).mul h2).mul h6

/-- Once a finite formal product contains all factors through index `d+1`,
its coefficient of degree `d` is stable. -/
theorem hauptmodulFormalEulerProduct_coeff_stable (d N : ℕ)
    (hN : d + 2 ≤ N) :
    PowerSeries.coeff d
      (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) =
    PowerSeries.coeff d
      (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hbase ih =>
      rw [show (∏ i ∈ Finset.range (N + 1), hauptmodulFormalEulerFactor (i + 1)) =
        (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) *
          hauptmodulFormalEulerFactor (N + 1) by
        simp only [Finset.prod_range_succ]]
      rw [coeff_mul_of_lowCoefficientsOne_right]
      · exact ih
      · intro j hj
        exact hauptmodulFormalEulerFactor_lowCoefficientsOne (N + 1) (by omega)
          j (by omega)


/-- Taylor expansion commutes with the finite product of analytic Euler
factors, and the result is the cast of the integral formal finite product. -/
theorem analyticTaylorPowerSeries_prod_factor (N : ℕ) :
    analyticTaylorPowerSeries
      (fun q => ∏ i ∈ Finset.range N,
        hauptmodulEulerAnalyticFactor q (i + 1)) =
    PowerSeries.map (Int.castRingHom ℂ)
      (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hfactor (m : ℕ) (hm : m ≠ 0) : AnalyticAt ℂ
          (fun q => hauptmodulEulerAnalyticFactor q m) 0 := by
        unfold hauptmodulEulerAnalyticFactor
        apply AnalyticAt.fun_mul
        · apply AnalyticAt.fun_mul
          · apply AnalyticAt.fun_mul <;> fun_prop
          · exact analyticAt_const.div
              (analyticAt_const.sub (analyticAt_id.pow (2 * m)))
              (by simp [hm])
        · exact analyticAt_const.div
            ((analyticAt_const.sub (analyticAt_id.pow (6 * m))).pow 5)
            (by simp [hm])
      have hprev : AnalyticAt ℂ
          (fun q => ∏ i ∈ Finset.range N,
            hauptmodulEulerAnalyticFactor q (i + 1)) 0 := by
        apply Finset.analyticAt_fun_prod
        intro i hi
        exact hfactor (i + 1) (by omega)
      have hlast : AnalyticAt ℂ
          (fun q => hauptmodulEulerAnalyticFactor q (N + 1)) 0 :=
        hfactor (N + 1) (by omega)
      rw [show (fun q => ∏ i ∈ Finset.range (N + 1),
          hauptmodulEulerAnalyticFactor q (i + 1)) =
        (fun q => (∏ i ∈ Finset.range N,
          hauptmodulEulerAnalyticFactor q (i + 1)) *
            hauptmodulEulerAnalyticFactor q (N + 1)) by
          funext q
          simp only [Finset.prod_range_succ]]
      rw [analyticTaylorPowerSeries_mul _ _ hprev hlast, ih]
      rw [show (∏ i ∈ Finset.range (N + 1),
          hauptmodulFormalEulerFactor (i + 1)) =
        (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) *
          hauptmodulFormalEulerFactor (N + 1) by
            simp only [Finset.prod_range_succ]]
      rw [map_mul, map_hauptmodulFormalEulerFactor (N + 1) (by omega)]
      rw [analyticTaylorPowerSeries_hauptmodulEulerAnalyticFactor
        (N + 1) (by omega)]

/-- Each finite simultaneous quotient has Taylor coefficients equal to the
cast of the independently constructed integral finite formal product. -/
theorem analyticTaylorPowerSeries_hauptmodulEulerPartial (N : ℕ) :
    analyticTaylorPowerSeries (fun q => hauptmodulEulerPartial q N) =
    PowerSeries.map (Int.castRingHom ℂ)
      (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) := by
  rw [show (fun q => hauptmodulEulerPartial q N) =
      (fun q => ∏ i ∈ Finset.range N,
        hauptmodulEulerAnalyticFactor q (i + 1)) by
    funext q
    exact hauptmodulEulerPartial_eq_prod_factor q N]
  exact analyticTaylorPowerSeries_prod_factor N

/-- The analytic Taylor coefficient of the disk Hauptmodul is exactly the
complex cast of the stabilized integral formal coefficient. -/
theorem hauptmodulEulerDisk_taylorCoeff_eq_formal (d : ℕ) :
    (d.factorial : ℂ)⁻¹ * iteratedDeriv d hauptmodulEulerDisk 0 =
      ((PowerSeries.coeff d hauptmodulFormalEulerUnit : ℤ) : ℂ) := by
  let c : ℂ := ((PowerSeries.coeff d hauptmodulFormalEulerUnit : ℤ) : ℂ)
  let s : ℕ → ℂ := fun N => (d.factorial : ℂ)⁻¹ *
    iteratedDeriv d (fun q => hauptmodulEulerPartial q N) 0
  have hsN (N : ℕ) : s N =
      ((PowerSeries.coeff d
        (∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)) : ℤ) : ℂ) := by
    let P : PowerSeries ℤ :=
      ∏ i ∈ Finset.range N, hauptmodulFormalEulerFactor (i + 1)
    calc
      s N = PowerSeries.coeff d
          (analyticTaylorPowerSeries (fun q => hauptmodulEulerPartial q N)) := by
        simp [s, analyticTaylorPowerSeries_coeff]
      _ = PowerSeries.coeff d (PowerSeries.map (Int.castRingHom ℂ) P) := by
        rw [analyticTaylorPowerSeries_hauptmodulEulerPartial]
      _ = ((PowerSeries.coeff d P : ℤ) : ℂ) := by
        rw [PowerSeries.coeff_map]
        rfl
      _ = _ := rfl
  have hevent : s =ᶠ[Filter.atTop] (fun _ => c) := by
    filter_upwards [Filter.eventually_ge_atTop (d + 2)] with N hN
    rw [hsN]
    rw [hauptmodulFormalEulerProduct_coeff_stable d N hN]
    rw [← hauptmodulFormalEulerUnit_coeff_stabilized d]
  have hcLim : Filter.Tendsto s Filter.atTop (nhds c) :=
    (tendsto_const_nhds.congr' hevent.symm)
  have haLim := hauptmodulEulerPartial_taylorCoeff_tendsto d
  exact tendsto_nhds_unique haLim hcLim

/-- The analytic disk Euler unit is represented on the whole unit disk by
its independently constructed integral formal Euler series. -/
theorem hauptmodulFormalEulerUnit_tsum_eq_disk {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((PowerSeries.coeff n hauptmodulFormalEulerUnit : ℤ) : ℂ) * q ^ n) =
      hauptmodulEulerDisk q := by
  rw [← hauptmodulEulerDisk_taylorSeries hq]
  apply tsum_congr
  intro n
  rw [hauptmodulEulerDisk_taylorCoeff_eq_formal]


/-- At every upper-half-plane nome, the actual Dedekind-eta Euler unit is the
sum of the integral stabilized formal Euler series. -/
theorem hauptmodulFormalEulerUnit_tsum_eq_eulerUnit (τ : UpperHalfPlane) :
    (∑' n : ℕ, ((PowerSeries.coeff n hauptmodulFormalEulerUnit : ℤ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) = hauptmodulEulerUnit τ := by
  rw [hauptmodulFormalEulerUnit_tsum_eq_disk (norm_qParam_lt_one τ)]
  exact hauptmodulEulerDisk_qParam τ

/-- Exact analytic/formal identification of the actual eta quotient: its
Laurent expansion is `q⁻¹` times the integral formal Euler unit. -/
theorem analyticHauptmodul_eq_integral_formal_expansion (τ : UpperHalfPlane) :
    SptCM.CM.Repaired.analyticHauptmodul τ =
      (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ *
        (∑' n : ℕ, ((PowerSeries.coeff n hauptmodulFormalEulerUnit : ℤ) : ℂ) *
          Function.Periodic.qParam 1 (τ : ℂ) ^ n) := by
  rw [analyticHauptmodul_eq_qParam_inv_mul_eulerUnit,
    hauptmodulFormalEulerUnit_tsum_eq_eulerUnit]

end SptCM.Repair
