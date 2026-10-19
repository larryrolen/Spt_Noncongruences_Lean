import blessed.SptCM.Analytic.Repaired.I05HeckeApplication
import blessed.SptCM.Analytic.PaperCoefficientModels

/-!
# Characteristic reduction of the source Hecke identities

The published grid has integral Fourier coefficients.  We retain that single
integral family and obtain both its characteristic-zero realization (where
modular-form uniqueness proves I05) and its reduction modulo a prime from it.
Thus no unrelated grid over `ZMod ℓ` is chosen.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic SptCM.RolenLiterature

/-- Coefficientwise casting of an integral Fourier series. -/
def castIntegralSeries (K : Type*) [Ring K] (f : QSeries ℤ) : QSeries K :=
  fun r => (f r : K)

/-- The actual integral quadratic symbol occurring in the Hecke formulas. -/
def integralHeckeLegendre (p : ℕ) (r : ℤ) : ℤ :=
  if hp : p.Prime then
    let _ : Fact p.Prime := ⟨hp⟩
    legendreSym p r
  else 0

lemma cast_integralHeckeLegendre
    {K : Type*} [Field K] (p : ℕ) (r : ℤ) :
    (integralHeckeLegendre p r : K) = actualHeckeLegendre p r := by
  by_cases hp : p.Prime
  · let _ : Fact p.Prime := ⟨hp⟩
    simp [integralHeckeLegendre, actualHeckeLegendre, hp,
      heckeLegendreCast]
  · simp [integralHeckeLegendre, actualHeckeLegendre, hp]

/-- The one integral published grid, together with its characteristic-zero
realization.  Integrality of the grid coefficients is part of the cited grid
theorem; the Hecke identities are not fields. -/
structure IntegralGridRealization where
  grid : ℕ → QSeries ℤ
  rationalGrid : PublishedMockModularGrid ℚ
  rational_grid : ∀ m r, rationalGrid.grid m r = (grid m r : ℚ)
  sourceQualification : SourceI05Qualification rationalGrid

/-- Reduction of the unique integral grid, rather than a fresh arbitrary grid
over the finite field. -/
def IntegralGridRealization.modGrid (D : IntegralGridRealization) (ℓ m : ℕ) :
    QSeries (ZMod ℓ) :=
  castIntegralSeries (ZMod ℓ) (D.grid m)

/-- The integral expansion of the first displayed Hecke expression. -/
def integralFHeckeDifference (p : ℕ) : QSeries ℤ := fun r =>
  fSeries ((p : ℤ) ^ 2 * r) +
    (chi12 (p : ℤ) : ℤ) * integralHeckeLegendre p (-r) * fSeries r +
    (if ((p : ℤ) ^ 2) ∣ r then
      (p : ℤ) * fSeries (r / (p : ℤ) ^ 2) else 0) -
    (chi12 (p : ℤ) : ℤ) * (1 + p) * fSeries r

lemma cast_integralFHeckeDifference
    {K : Type*} [Field K] (p : ℕ) :
    castIntegralSeries K (integralFHeckeDifference p) =
      fHeckeDifference p (chi12 p : K) (actualHeckeLegendre p)
        (castIntegralSeries K fSeries) := by
  funext r
  simp only [castIntegralSeries, integralFHeckeDifference,
    fHeckeDifference, heckeThreeHalf]
  push_cast
  rw [cast_integralHeckeLegendre]

/-- The first displayed I05 identity already holds over the integers.  It is
obtained from the rational identity by injectivity of `ℤ → ℚ`; no modular
identity is assumed. -/
theorem integral_f_hecke_identity
    (D : IntegralGridRealization) (p : ℕ) (hp : ValidLevelPrime p) :
    integralFHeckeDifference p = fun r => (p : ℤ) * D.grid p r := by
  funext r
  have h := congrFun
    (actual_f_hecke_identity_displayed D.rationalGrid
      D.sourceQualification p hp) r
  have hchi := D.rationalGrid.chi_eq_chi12 p
  have hgrid := D.rational_grid p r
  change fHeckeDifference p (D.rationalGrid.chi p)
      (actualHeckeLegendre p) (castIntegralSeries ℚ fSeries) r =
    (p : ℚ) * D.rationalGrid.grid p r at h
  have hcast := congrFun (cast_integralFHeckeDifference (K := ℚ) p) r
  rw [hchi, ← hcast, castIntegralSeries, hgrid] at h
  exact_mod_cast h

/-- Coefficientwise reduction of the actual first I05 identity modulo any
prime. -/
theorem mod_f_hecke_identity
    (D : IntegralGridRealization) (ℓ p : ℕ) [Fact ℓ.Prime]
    (hp : ValidLevelPrime p) :
    fHeckeDifference p (chi12 p : ZMod ℓ)
        (actualHeckeLegendre p) (fSeriesMod ℓ) =
      fun r => (p : ZMod ℓ) * D.modGrid ℓ p r := by
  have h := integral_f_hecke_identity D p hp
  funext r
  have hr := congrArg (fun z : ℤ => (z : ZMod ℓ)) (congrFun h r)
  have hcast := congrFun (cast_integralFHeckeDifference (K := ZMod ℓ) p) r
  change fHeckeDifference p (chi12 p : ZMod ℓ)
      (actualHeckeLegendre p) (castIntegralSeries (ZMod ℓ) fSeries) r = _
  rw [← hcast]
  simpa [castIntegralSeries, fSeriesMod, IntegralGridRealization.modGrid]
    using hr

/-- Integral coefficient formula underlying the weight `3/2` Hecke operator. -/
def integralHeckeThreeHalf (p : ℕ) (chiP : ℤ) (legendre : ℤ → ℤ)
    (g : QSeries ℤ) : QSeries ℤ := fun r =>
  g ((p : ℤ) ^ 2 * r) + chiP * legendre (-r) * g r +
    if ((p : ℤ) ^ 2) ∣ r then (p : ℤ) * g (r / (p : ℤ) ^ 2) else 0

lemma cast_integralHeckeThreeHalf
    {K : Type*} [Field K] (p : ℕ) (chiP : ℤ) (legendre : ℤ → ℤ)
    (g : QSeries ℤ) :
    castIntegralSeries K (integralHeckeThreeHalf p chiP legendre g) =
      heckeThreeHalf p (chiP : K) (fun r => (legendre r : K))
        (castIntegralSeries K g) := by
  funext r
  simp only [castIntegralSeries, integralHeckeThreeHalf, heckeThreeHalf]
  by_cases hdiv : ((p : ℤ) ^ 2) ∣ r <;> simp [hdiv]

/-- Integral version of the conventionally zero divided-index grid term. -/
def integralGridDivisorTerm (D : IntegralGridRealization) (m p : ℕ) :
    QSeries ℤ :=
  if p ∣ m then D.grid (m / p) else 0

lemma cast_integralGridDivisorTerm
    {K : Type*} [Field K] (D : IntegralGridRealization) (m p : ℕ) :
    castIntegralSeries K (integralGridDivisorTerm D m p) =
      gridDivisorTerm (fun a => castIntegralSeries K (D.grid a)) m p := by
  by_cases hpm : p ∣ m
  · funext r
    simp [integralGridDivisorTerm, gridDivisorTerm, hpm, castIntegralSeries]
  · funext r
    simp [integralGridDivisorTerm, gridDivisorTerm, hpm, castIntegralSeries]

/-- The integral right side of the second displayed I05 identity. -/
def integralGridHeckeRight (D : IntegralGridRealization) (m p : ℕ) :
    QSeries ℤ := fun r =>
  (p : ℤ) * D.grid (m * p) r +
    (chi12 (p : ℤ) : ℤ) * integralHeckeLegendre p ((m : ℤ) ^ 2) *
      D.grid m r +
    integralGridDivisorTerm D m p r -
    (p : ℤ) * (chi12 (m : ℤ) : ℤ) * D.grid p r

/-- The second displayed grid recurrence holds coefficientwise over `ℤ`, by
injectivity of the rational realization. -/
theorem integral_grid_hecke_identity
    (D : IntegralGridRealization) (m p : ℕ)
    (hm : 1 < m) (hm6 : Nat.Coprime m 6) (hp : ValidLevelPrime p) :
    integralHeckeThreeHalf p (chi12 (p : ℤ))
        (integralHeckeLegendre p) (D.grid m) =
      integralGridHeckeRight D m p := by
  funext r
  have h := congrFun
    (actual_grid_hecke_identity_displayed D.rationalGrid
      D.sourceQualification m p hm hm6 hp) r
  have hgm : D.rationalGrid.grid m = castIntegralSeries ℚ (D.grid m) := by
    funext s
    exact D.rational_grid m s
  rw [hgm] at h
  rw [D.rationalGrid.chi_eq_chi12 p,
    show (chi12 p : ℚ) = (chi12 (p : ℤ) : ℤ) by rfl,
    ← cast_integralHeckeLegendre (K := ℚ) p] at h
  have hlegQ : (fun s => (integralHeckeLegendre p s : ℚ)) =
      actualHeckeLegendre p := by
    funext s
    exact cast_integralHeckeLegendre p s
  rw [← hlegQ] at h
  have hleft := congrFun
    (cast_integralHeckeThreeHalf (K := ℚ) p (chi12 (p : ℤ))
      (integralHeckeLegendre p) (D.grid m)) r
  rw [← hleft] at h
  simp only [integralGridHeckeRight]
  have hdiv := congrFun (cast_integralGridDivisorTerm (K := ℚ) D m p) r
  simp only [castIntegralSeries] at hdiv
  rw [D.rational_grid (m * p) r, D.rationalGrid.chi_eq_chi12 m,
    D.rational_grid p r] at h
  -- Replace the rational divided-index term by the cast of the same integral
  -- convention, then use injectivity of `ℤ → ℚ`.
  have hdiv' : gridDivisorTerm D.rationalGrid.grid m p r =
      (integralGridDivisorTerm D m p r : ℚ) := by
    by_cases hpm : p ∣ m
    · simp [gridDivisorTerm, integralGridDivisorTerm, hpm,
        D.rational_grid]
    · simp [gridDivisorTerm, integralGridDivisorTerm, hpm]
  rw [hdiv'] at h
  simp only [castIntegralSeries] at h
  exact_mod_cast h

/-- Reduction of the actual grid recurrence to characteristic `ℓ`. -/
theorem mod_grid_hecke_identity
    (D : IntegralGridRealization) (ℓ m p : ℕ) [Fact ℓ.Prime]
    (hm : 1 < m) (hm6 : Nat.Coprime m 6) (hp : ValidLevelPrime p) :
    heckeThreeHalf p (chi12 p : ZMod ℓ) (actualHeckeLegendre p)
        (D.modGrid ℓ m) =
      fun r =>
        (p : ZMod ℓ) * D.modGrid ℓ (m * p) r +
        (chi12 p : ZMod ℓ) * actualHeckeLegendre p ((m : ℤ) ^ 2) *
          D.modGrid ℓ m r +
        gridDivisorTerm (D.modGrid ℓ) m p r -
        (p : ZMod ℓ) * (chi12 m : ZMod ℓ) * D.modGrid ℓ p r := by
  have h := integral_grid_hecke_identity D m p hm hm6 hp
  funext r
  have hr := congrArg (fun z : ℤ => (z : ZMod ℓ)) (congrFun h r)
  have hleft := congrFun
    (cast_integralHeckeThreeHalf (K := ZMod ℓ) p (chi12 (p : ℤ))
      (integralHeckeLegendre p) (D.grid m)) r
  have hdiv := congrFun
    (cast_integralGridDivisorTerm (K := ZMod ℓ) D m p) r
  have hleg : (fun s => (integralHeckeLegendre p s : ZMod ℓ)) =
      actualHeckeLegendre p := by
    funext s
    exact cast_integralHeckeLegendre p s
  rw [hleg] at hleft
  rw [show D.modGrid ℓ =
    (fun a => castIntegralSeries (ZMod ℓ) (D.grid a)) from rfl]
  rw [← hleft]
  rw [← cast_integralHeckeLegendre (K := ZMod ℓ) p ((m : ℤ) ^ 2)]
  rw [← hdiv]
  simp only [integralGridHeckeRight] at hr
  push_cast at hr
  simpa [castIntegralSeries, IntegralGridRealization.modGrid] using hr

/-- A valid Hecke prime is nonzero in the characteristic field. -/
lemma validHeckePrime_cast_ne_zero
    (ℓ p : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p) :
    (p : ZMod ℓ) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff]
  intro hdiv
  have hcop : Nat.Coprime p ℓ :=
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_left ℓ 6) hp.2
  have := hcop.symm.eq_one_of_dvd hdiv
  omega

/-- Fermat's theorem gives invariance of the theta-cycle diagonal weight when
an index is multiplied by a valid Hecke-prime square. -/
theorem thetaCycleWeight_mul_prime_sq
    (ℓ p : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p)
    (n : ℤ) :
    (((((p : ℤ) ^ 2 * n : ℤ) : ZMod ℓ) / (24 : ZMod ℓ)) ^
        ((ℓ - 1) / 2)) =
      (((n : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)) := by
  let k := (ℓ - 1) / 2
  have hodd : ℓ % 2 = 1 :=
    (Fact.out : ℓ.Prime).eq_two_or_odd.resolve_left (by omega)
  have htwok : 2 * k = ℓ - 1 := by
    dsimp [k]
    omega
  have hp0 : (p : ZMod ℓ) ≠ 0 := validHeckePrime_cast_ne_zero ℓ p hℓ hp
  have hfermat : (p : ZMod ℓ) ^ (ℓ - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hp0
  push_cast
  change ((((p : ZMod ℓ) ^ 2 * (n : ZMod ℓ)) / 24) ^ k) = _
  rw [mul_div_assoc, mul_pow, ← pow_mul, htwok, hfermat, one_mul]

/-- The corresponding divided-index weight relation. -/
theorem thetaCycleWeight_div_prime_sq
    (ℓ p : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p)
    (n : ℤ) (hdiv : ((p : ℤ) ^ 2) ∣ n) :
    ((((n / ((p : ℤ) ^ 2) : ℤ) : ZMod ℓ) / (24 : ZMod ℓ)) ^
        ((ℓ - 1) / 2)) =
      (((n : ZMod ℓ) / (24 : ZMod ℓ)) ^ ((ℓ - 1) / 2)) := by
  obtain ⟨z, rfl⟩ := hdiv
  rw [Int.mul_ediv_cancel_left z (pow_ne_zero 2 (by exact_mod_cast hp.1.ne_zero))]
  exact (thetaCycleWeight_mul_prime_sq ℓ p hℓ hp z).symm

/-- Hence the actual coefficient-formula Hecke operator commutes with the
paper's theta-cycle operator in exactly the range `p ∤ 6ℓ`. -/
theorem actualHecke_thetaCycle_commute
    (ℓ p : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p) :
    (fun g => thetaPowerSeriesOp ℓ ((ℓ - 1) / 2)
      (heckeThreeHalf p (chi12 p : ZMod ℓ) (actualHeckeLegendre p) g)) =
    (fun g => heckeThreeHalf p (chi12 p : ZMod ℓ)
      (actualHeckeLegendre p)
      (thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) g)) :=
  heckeThetaCycleCommute_of_weight_relations ℓ p _ _
    (thetaCycleWeight_mul_prime_sq ℓ p hℓ hp)
    (thetaCycleWeight_div_prime_sq ℓ p hℓ hp)

/-- Membership in the paper's theta-cycle eigenspace, stated directly on the
coefficient series used throughout this development. -/
def HasPaperThetaCycle (ℓ : ℕ) [Fact ℓ.Prime]
    (g : QSeries (ZMod ℓ)) : Prop :=
  thetaPowerSeriesOp ℓ ((ℓ - 1) / 2) g = thetaCycleEigenvalue ℓ • g

lemma hasPaperThetaCycle_zero (ℓ : ℕ) [Fact ℓ.Prime] :
    HasPaperThetaCycle ℓ (0 : QSeries (ZMod ℓ)) := by
  funext r
  simp [thetaPowerSeriesOp]

lemma HasPaperThetaCycle.smul
    {ℓ : ℕ} [Fact ℓ.Prime] {g : QSeries (ZMod ℓ)}
    (hg : HasPaperThetaCycle ℓ g) (c : ZMod ℓ) :
    HasPaperThetaCycle ℓ (c • g) := by
  rw [HasPaperThetaCycle] at hg ⊢
  funext r
  have hr := congrFun hg r
  simp only [thetaPowerSeriesOp_apply, Pi.smul_apply, smul_eq_mul] at hr ⊢
  linear_combination c * hr

lemma HasPaperThetaCycle.add
    {ℓ : ℕ} [Fact ℓ.Prime] {g h : QSeries (ZMod ℓ)}
    (hg : HasPaperThetaCycle ℓ g) (hh : HasPaperThetaCycle ℓ h) :
    HasPaperThetaCycle ℓ (g + h) := by
  rw [HasPaperThetaCycle] at hg hh ⊢
  funext r
  have hgr := congrFun hg r
  have hhr := congrFun hh r
  simp only [thetaPowerSeriesOp_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hgr hhr ⊢
  linear_combination hgr + hhr

lemma HasPaperThetaCycle.sub
    {ℓ : ℕ} [Fact ℓ.Prime] {g h : QSeries (ZMod ℓ)}
    (hg : HasPaperThetaCycle ℓ g) (hh : HasPaperThetaCycle ℓ h) :
    HasPaperThetaCycle ℓ (g - h) := by
  rw [HasPaperThetaCycle] at hg hh ⊢
  funext r
  have hgr := congrFun hg r
  have hhr := congrFun hh r
  simp only [thetaPowerSeriesOp_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at hgr hhr ⊢
  linear_combination hgr - hhr

lemma HasPaperThetaCycle.cancel_smul
    {ℓ : ℕ} [Fact ℓ.Prime] {g : QSeries (ZMod ℓ)} {c : ZMod ℓ}
    (hc : c ≠ 0) (hcg : HasPaperThetaCycle ℓ (c • g)) :
    HasPaperThetaCycle ℓ g := by
  rw [HasPaperThetaCycle] at hcg ⊢
  funext r
  have hr := congrFun hcg r
  simp only [thetaPowerSeriesOp_apply, Pi.smul_apply, smul_eq_mul] at hr ⊢
  apply mul_left_cancel₀ hc
  linear_combination hr

/-- Commutation in the valid prime range preserves the theta-cycle space. -/
theorem hasPaperThetaCycle_hecke
    (ℓ p : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p)
    {g : QSeries (ZMod ℓ)} (hg : HasPaperThetaCycle ℓ g) :
    HasPaperThetaCycle ℓ
      (heckeThreeHalf p (chi12 p : ZMod ℓ) (actualHeckeLegendre p) g) := by
  rw [HasPaperThetaCycle] at hg ⊢
  have hc := congrFun (actualHecke_thetaCycle_commute ℓ p hℓ hp) g
  rw [hc, hg]
  funext r
  simp only [heckeThreeHalf, Pi.smul_apply, smul_eq_mul]
  by_cases hdiv : ((p : ℤ) ^ 2) ∣ r <;> simp [hdiv] <;> ring

/-- Prime base case: reduction of the first actual I05 identity transports the
Ahlgren--Kim theta cycle from `f` to the reduced integral grid member `G_p`. -/
theorem prime_modGrid_theta_support
    (D : IntegralGridRealization) (ℓ p : ℕ) [Fact ℓ.Prime]
    (hℓ : 5 ≤ ℓ) (hp : ValidHeckePrime ℓ p)
    (hf : HasPaperThetaCycle ℓ (fSeriesMod ℓ)) :
    HasPaperThetaCycle ℓ (D.modGrid ℓ p) := by
  have hpLevel : ValidLevelPrime p := ⟨hp.1,
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hp.2⟩
  have hid := mod_f_hecke_identity D ℓ p hpLevel
  have hhecke := hasPaperThetaCycle_hecke ℓ p hℓ hp hf
  have hscalar := hf.smul ((chi12 p : ZMod ℓ) * (1 + p))
  have hdiff :
      fHeckeDifference p (chi12 p : ZMod ℓ) (actualHeckeLegendre p)
          (fSeriesMod ℓ) =
        heckeThreeHalf p (chi12 p : ZMod ℓ) (actualHeckeLegendre p)
            (fSeriesMod ℓ) -
          ((chi12 p : ZMod ℓ) * (1 + p)) • fSeriesMod ℓ := by
    funext r
    simp [fHeckeDifference, Pi.smul_apply, smul_eq_mul]
  have hleft : HasPaperThetaCycle ℓ
      (fHeckeDifference p (chi12 p : ZMod ℓ) (actualHeckeLegendre p)
        (fSeriesMod ℓ)) := by
    rw [hdiff]
    exact hhecke.sub hscalar
  rw [hid] at hleft
  have heq : (fun r => (p : ZMod ℓ) * D.modGrid ℓ p r) =
      (p : ZMod ℓ) • D.modGrid ℓ p := by
    rfl
  rw [heq] at hleft
  exact hleft.cancel_smul (validHeckePrime_cast_ne_zero ℓ p hℓ hp)

/-- I02, corrected recursion: the reduced actual grid recurrence propagates
theta support at a valid Hecke prime.  Support of the divided-index term and
of the prime grid member are explicit earlier-index premises, not assumptions
about the desired `G_{mp}`. -/
theorem actual_modGrid_theta_recursion
    (D : IntegralGridRealization) (ℓ m p : ℕ) [Fact ℓ.Prime]
    (hℓ : 5 ≤ ℓ) (hm : 1 < m) (hmAllowed : ValidGridIndex ℓ m)
    (hp : ValidHeckePrime ℓ p)
    (hGm : HasPaperThetaCycle ℓ (D.modGrid ℓ m))
    (hGp : HasPaperThetaCycle ℓ (D.modGrid ℓ p))
    (hGdiv : p ∣ m → HasPaperThetaCycle ℓ (D.modGrid ℓ (m / p))) :
    HasPaperThetaCycle ℓ (D.modGrid ℓ (m * p)) := by
  have hm6 : Nat.Coprime m 6 :=
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hmAllowed
  have hpLevel : ValidLevelPrime p := ⟨hp.1,
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hp.2⟩
  have hid := mod_grid_hecke_identity D ℓ m p hm hm6 hpLevel
  have hhecke := hasPaperThetaCycle_hecke ℓ p hℓ hp hGm
  have hdivCycle : HasPaperThetaCycle ℓ
      (gridDivisorTerm (D.modGrid ℓ) m p) := by
    by_cases hpm : p ∣ m
    · simp only [gridDivisorTerm, hpm, if_true]
      exact hGdiv hpm
    · simp [gridDivisorTerm, hpm, hasPaperThetaCycle_zero]
  let a : ZMod ℓ :=
    (chi12 p : ZMod ℓ) * actualHeckeLegendre p ((m : ℤ) ^ 2)
  let b : ZMod ℓ := (p : ZMod ℓ) * (chi12 m : ZMod ℓ)
  let rem : QSeries (ZMod ℓ) :=
    a • D.modGrid ℓ m + gridDivisorTerm (D.modGrid ℓ) m p -
      b • D.modGrid ℓ p
  have hrem : HasPaperThetaCycle ℓ rem :=
    (hGm.smul a).add hdivCycle |>.sub (hGp.smul b)
  have hid' :
      heckeThreeHalf p (chi12 p : ZMod ℓ) (actualHeckeLegendre p)
          (D.modGrid ℓ m) =
        (p : ZMod ℓ) • D.modGrid ℓ (m * p) + rem := by
    rw [hid]
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      a, b, rem]
    ring
  have hscaled : HasPaperThetaCycle ℓ
      ((p : ZMod ℓ) • D.modGrid ℓ (m * p)) := by
    rw [← sub_eq_iff_eq_add.mpr hid']
    exact hhecke.sub hrem
  exact hscaled.cancel_smul (validHeckePrime_cast_ne_zero ℓ p hℓ hp)

lemma integralGrid_one (D : IntegralGridRealization) : D.grid 1 = 0 := by
  funext r
  have h := D.rational_grid 1 r
  rw [D.rationalGrid.grid_one] at h
  simp only [Pi.zero_apply] at h
  exact_mod_cast h.symm

@[simp] lemma IntegralGridRealization.modGrid_one
    (D : IntegralGridRealization) (ℓ : ℕ) : D.modGrid ℓ 1 = 0 := by
  rw [IntegralGridRealization.modGrid, integralGrid_one]
  funext r
  simp [castIntegralSeries]

/-- I06: every member of the actual integral published grid whose index is
coprime to `6ℓ` has, after reduction, the same theta-cycle eigenvalue as `f`.
The proof is strong induction: primes use the first I05 identity, and a
composite index is reached from a smaller quotient using the corrected I02
recursion; its divided-index correction is smaller again. -/
theorem actual_modGrid_theta_support
    (D : IntegralGridRealization) (ℓ m : ℕ) [Fact ℓ.Prime]
    (hℓ : 5 ≤ ℓ) (hmAllowed : ValidGridIndex ℓ m)
    (hf : HasPaperThetaCycle ℓ (fSeriesMod ℓ)) :
    HasPaperThetaCycle ℓ (D.modGrid ℓ m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        rw [D.modGrid_one]
        exact hasPaperThetaCycle_zero ℓ
      have hmpos : 0 < m := by
        have hm6 : Nat.Coprime m 6 :=
          Nat.Coprime.of_dvd_right (Nat.dvd_mul_right 6 ℓ) hmAllowed
        exact Nat.pos_of_ne_zero (fun hm0 => by subst m; simp at hm6)
      by_cases hmprime : m.Prime
      · exact prime_modGrid_theta_support D ℓ m hℓ
          ⟨hmprime, hmAllowed⟩ hf
      let p := m.minFac
      let q := m / p
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have hpAllowed : ValidGridIndex ℓ p :=
        Nat.Coprime.of_dvd_left hpdvd hmAllowed
      have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hmpos hpdvd) hp.pos
      have hmq : q * p = m := by
        simpa [q, p, Nat.mul_comm] using Nat.div_mul_cancel hpdvd
      have hq1 : 1 < q := by
        by_contra hnot
        have hqeq : q = 1 := by omega
        apply hmprime
        rw [← hmq, hqeq, one_mul]
        exact hp
      have hqlt : q < m := by
        rw [← hmq]
        nlinarith [hp.one_lt]
      have hqAllowed : ValidGridIndex ℓ q :=
        Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hpdvd) hmAllowed
      have hGq : HasPaperThetaCycle ℓ (D.modGrid ℓ q) :=
        ih q hqlt hqAllowed
      have hGp : HasPaperThetaCycle ℓ (D.modGrid ℓ p) :=
        prime_modGrid_theta_support D ℓ p hℓ ⟨hp, hpAllowed⟩ hf
      have hGdiv : p ∣ q → HasPaperThetaCycle ℓ (D.modGrid ℓ (q / p)) := by
        intro hpq
        have hdivpos : 0 < q / p :=
          Nat.div_pos (Nat.le_of_dvd hqpos hpq) hp.pos
        have hdivltq : q / p < q := Nat.div_lt_self hqpos hp.one_lt
        have hdivlt : q / p < m := hdivltq.trans hqlt
        have hdivAllowed : ValidGridIndex ℓ (q / p) :=
          Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hpq) hqAllowed
        exact ih (q / p) hdivlt hdivAllowed
      have hstep := actual_modGrid_theta_recursion D ℓ q p hℓ hq1
        hqAllowed ⟨hp, hpAllowed⟩ hGq hGp hGdiv
      simpa [hmq] using hstep

end SptCM.Analytic.Repaired
