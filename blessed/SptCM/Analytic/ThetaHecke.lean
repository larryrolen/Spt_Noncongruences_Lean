import Mathlib

/-!
# Abstract theta--Hecke deductions

This module formalizes the linear-algebraic content of Section 2 of the paper.
The genuinely analytic inputs (the Ahlgren--Kim theta-cycle theorem and the
shadow/Hecke intertwining theorem cited from the harmonic-Maass-form
literature) occur only as explicit hypotheses.  The deductions from those
inputs -- coefficient vanishing, passage through a commuting Hecke operator,
and solving the grid recurrences -- are proved here.
-/

namespace SptCM.Analytic

/-- An element is in the `ε`-eigenspace of the theta-cycle operator. -/
def IsThetaEigen {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (theta : V →ₗ[K] V) (ε : K) (x : V) : Prop :=
  theta x = ε • x

/-- The exact external assertion supplied by the Ahlgren--Kim theta-cycle
result, separated from its coefficientwise consequences. -/
def AhlgrenKimThetaCycleInput
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (theta : V →ₗ[K] V) (ε : K) (f : V) : Prop :=
  IsThetaEigen theta ε f

/-- Theta eigenvectors are closed under scalar multiplication. -/
theorem IsThetaEigen.smul
    {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    {theta : V →ₗ[K] V} {ε c : K} {x : V}
    (hx : IsThetaEigen theta ε x) :
    IsThetaEigen theta ε (c • x) := by
  rw [IsThetaEigen] at hx ⊢
  rw [LinearMap.map_smul, hx, smul_smul, smul_smul, mul_comm c ε]

/-- Theta eigenvectors are closed under addition. -/
theorem IsThetaEigen.add
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    {theta : V →ₗ[K] V} {ε : K} {x y : V}
    (hx : IsThetaEigen theta ε x) (hy : IsThetaEigen theta ε y) :
    IsThetaEigen theta ε (x + y) := by
  rw [IsThetaEigen] at hx hy ⊢
  rw [LinearMap.map_add, hx, hy, smul_add]

/-- Theta eigenvectors are closed under subtraction. -/
theorem IsThetaEigen.sub
    {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {theta : V →ₗ[K] V} {ε : K} {x y : V}
    (hx : IsThetaEigen theta ε x) (hy : IsThetaEigen theta ε y) :
    IsThetaEigen theta ε (x - y) := by
  rw [IsThetaEigen] at hx hy ⊢
  rw [LinearMap.map_sub, hx, hy, smul_sub]

/-- A Hecke operator commuting with theta preserves the theta eigenspace. -/
theorem thetaEigen_hecke
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    {theta hecke : V →ₗ[K] V} {ε : K} {x : V}
    (hcomm : theta.comp hecke = hecke.comp theta)
    (hx : IsThetaEigen theta ε x) :
    IsThetaEigen theta ε (hecke x) := by
  rw [IsThetaEigen] at hx ⊢
  have happ := LinearMap.congr_fun hcomm x
  calc
    theta (hecke x) = hecke (theta x) := by simpa [LinearMap.comp_apply] using happ
    _ = hecke (ε • x) := by rw [hx]
    _ = ε • hecke x := by rw [LinearMap.map_smul]

/-- The elementary step behind both Hecke identities: if `H x = c • y + z`,
`H` commutes with theta, `x` and `z` are theta eigenvectors, and `c ≠ 0`,
then `y` is a theta eigenvector. -/
theorem thetaEigen_of_hecke_solve
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta hecke : V →ₗ[K] V} {ε c : K} {x y z : V}
    (hc : c ≠ 0)
    (hcomm : theta.comp hecke = hecke.comp theta)
    (hx : IsThetaEigen theta ε x)
    (hz : IsThetaEigen theta ε z)
    (hrel : hecke x = c • y + z) :
    IsThetaEigen theta ε y := by
  have hhecke : IsThetaEigen theta ε (hecke x) := thetaEigen_hecke hcomm hx
  have hcy : IsThetaEigen theta ε (c • y) := by
    rw [← sub_eq_iff_eq_add.mpr hrel]
    exact hhecke.sub hz
  rw [IsThetaEigen] at hcy ⊢
  rw [LinearMap.map_smul, smul_smul] at hcy
  have hinv := congrArg (fun v : V => c⁻¹ • v) hcy
  simpa [smul_smul, hc, mul_assoc, mul_comm, mul_left_comm] using hinv

/-- The first grid step in the paper.  This is the internal deduction from the
Hecke identity `H f - a f = c G` and commuting of theta with `H`; the analytic
proof of those two premises is not hidden in the conclusion. -/
theorem thetaEigen_grid_of_f_hecke_identity
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta hecke : V →ₗ[K] V} {ε a c : K} {f G : V}
    (hc : c ≠ 0)
    (hcomm : theta.comp hecke = hecke.comp theta)
    (hf : AhlgrenKimThetaCycleInput theta ε f)
    (hidentity : hecke f - a • f = c • G) :
    IsThetaEigen theta ε G := by
  apply thetaEigen_of_hecke_solve hc hcomm hf (IsThetaEigen.smul hf)
  exact sub_eq_iff_eq_add.mp hidentity

/-- The induction step used with the `G_m` Hecke recurrence: once the remaining
terms of the recurrence are known eigenvectors, one solves for `G_{mp}`. -/
theorem thetaEigen_grid_recurrence_step
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta hecke : V →ₗ[K] V} {ε c : K} {Gm Gmp remainder : V}
    (hc : c ≠ 0)
    (hcomm : theta.comp hecke = hecke.comp theta)
    (hm : IsThetaEigen theta ε Gm)
    (hrem : IsThetaEigen theta ε remainder)
    (hrec : hecke Gm = c • Gmp + remainder) :
    IsThetaEigen theta ε Gmp :=
  thetaEigen_of_hecke_solve hc hcomm hm hrem hrec

/-- Coefficient comparison: at an index where the diagonal theta eigenvalue is
not `ε`, the coefficient of an `ε`-eigenvector vanishes. -/
theorem coefficient_eq_zero_of_theta_eigenvalue_ne
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta : V →ₗ[K] V} {coeff : V →ₗ[K] K}
    {ε eigenvalue : K} {x : V}
    (hx : IsThetaEigen theta ε x)
    (hdiag : coeff (theta x) = eigenvalue * coeff x)
    (hne : eigenvalue ≠ ε) :
    coeff x = 0 := by
  have heq : eigenvalue * coeff x = ε * coeff x := by
    rw [← hdiag, hx, LinearMap.map_smul, smul_eq_mul]
  have hmul : (eigenvalue - ε) * coeff x = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

/-- In particular, the Ahlgren--Kim input yields its stated vanishing
consequence as soon as Euler's criterion identifies a mismatching diagonal
character at the coefficient in question. -/
theorem coefficient_eq_zero_of_ahlgrenKim_input
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta : V →ₗ[K] V} {coeff : V →ₗ[K] K}
    {ε eigenvalue : K} {f : V}
    (hAK : AhlgrenKimThetaCycleInput theta ε f)
    (hEuler : coeff (theta f) = eigenvalue * coeff f)
    (hcharacter : eigenvalue ≠ ε) :
    coeff f = 0 :=
  coefficient_eq_zero_of_theta_eigenvalue_ne hAK hEuler hcharacter


section CoefficientModels

/-- A coefficient model for the fractional-power `q`-series in Section 2;
the integer key is the numerator of the exponent `n/24`. -/
abbrev QSeries (K : Type*) := ℤ → K

/-- The principal-part predicate characterizing the canonical grid form.  It
states only the two negative coefficients used in the paper and vanishing of
all other negative coefficients. -/
def HasGridPrincipalPart {K : Type*} [Ring K]
    (chi : ℕ → K) (m : ℕ) (g : QSeries K) : Prop :=
  ∀ r : ℤ, r < 0 →
    g r = if r = -(m : ℤ) ^ 2 then 1
      else if r = -1 then -chi m else 0

/-- Chosen coefficient data for the grid; no modularity or existence is
asserted by this definition. -/
structure GridFormData (K : Type*) [Ring K] where
  chi : ℕ → K
  form : ℕ → QSeries K
  form_one : form 1 = 0
  principalPart : ∀ m, 1 < m → HasGridPrincipalPart chi m (form m)

/-- The chosen canonical grid form. -/
def gridForm {K : Type*} [Ring K] (data : GridFormData K) (m : ℕ) : QSeries K :=
  data.form m

@[simp] theorem gridForm_one {K : Type*} [Ring K] (data : GridFormData K) :
    gridForm data 1 = 0 := data.form_one

/-- Abstract existence-and-uniqueness step used by the paper after triangular
construction.  The caller supplies the genuine modular-form predicate and the
proved uniqueness implication; this theorem does not claim such a theory is
already present in Mathlib. -/
theorem gridForm_existsUnique
    {K : Type*} [Ring K] (data : GridFormData K) (m : ℕ) (hm : 1 < m)
    (IsModular : QSeries K → Prop)
    (hmod : IsModular (gridForm data m))
    (hunique : ∀ g, IsModular g → HasGridPrincipalPart data.chi m g →
      g = gridForm data m) :
    ∃! g, IsModular g ∧ HasGridPrincipalPart data.chi m g := by
  refine ⟨gridForm data m, ⟨hmod, data.principalPart m hm⟩, ?_⟩
  rintro g ⟨hgmod, hgpp⟩
  exact hunique g hgmod hgpp

/-- The coefficient formula for the paper's weight `3/2` Hecke operator.
Inadmissible divided indices contribute zero. -/
def heckeThreeHalf {K : Type*} [Field K]
    (ell : ℕ) (chiEll : K) (legendre : ℤ → K) (g : QSeries K) : QSeries K :=
  fun n =>
    g (((ell : ℤ) ^ 2) * n) + chiEll * legendre (-n) * g n +
      if ((ell : ℤ) ^ 2) ∣ n then (ell : K) * g (n / (ell : ℤ) ^ 2) else 0

/-- The coefficient formula for the dual weight `1/2` Hecke operator. -/
def heckeOneHalf {K : Type*} [Field K]
    (ell : ℕ) (chiEll : K) (legendre : ℤ → K) (g : QSeries K) : QSeries K :=
  fun n =>
    g (((ell : ℤ) ^ 2) * n) + (ell : K)⁻¹ * chiEll * legendre n * g n +
      if ((ell : ℤ) ^ 2) ∣ n then (ell : K)⁻¹ * g (n / (ell : ℤ) ^ 2) else 0

/-- The coefficient calculation behind
`η | T_{1/2}(ell²) = χ(ell) (1 + ell⁻¹) η`.

The hypotheses are the four elementary consequences of Euler's theta-series
formula for `η`: scaling a square index by `ell²`, the two values of the
quadratic symbol according as `ell²` divides the index, and removing `ell²`
from a supported square.  Thus this lemma proves the Hecke eigenform identity
from coefficient arithmetic rather than assuming the final identity. -/
theorem etaTheta_heckeOneHalf_eigen_of_coefficient_relations
    {K : Type*} [Field K]
    (ell : ℕ) (chiEll : K) (legendre : ℤ → K) (eta : QSeries K)
    (hchi_sq : chiEll ^ 2 = 1)
    (hscale : ∀ n : ℤ, eta (((ell : ℤ) ^ 2) * n) = chiEll * eta n)
    (hlegendre_dvd : ∀ n : ℤ, ((ell : ℤ) ^ 2) ∣ n →
      legendre n * eta n = 0)
    (hlegendre_not_dvd : ∀ n : ℤ, ¬((ell : ℤ) ^ 2) ∣ n →
      legendre n * eta n = eta n)
    (hremove : ∀ n : ℤ, ((ell : ℤ) ^ 2) ∣ n →
      chiEll * eta (n / (ell : ℤ) ^ 2) = eta n) :
    heckeOneHalf ell chiEll legendre eta =
      fun n => chiEll * (1 + (ell : K)⁻¹) * eta n := by
  funext n
  rw [heckeOneHalf, hscale]
  by_cases hdiv : ((ell : ℤ) ^ 2) ∣ n
  · have hremove' :
        eta (n / (ell : ℤ) ^ 2) = chiEll * eta n := by
      calc
        eta (n / (ell : ℤ) ^ 2) =
            chiEll ^ 2 * eta (n / (ell : ℤ) ^ 2) := by rw [hchi_sq]; simp
        _ = chiEll * (chiEll * eta (n / (ell : ℤ) ^ 2)) := by ring
        _ = chiEll * eta n := by rw [hremove n hdiv]
    rw [if_pos hdiv, hremove']
    have hleg := hlegendre_dvd n hdiv
    calc
      chiEll * eta n + (ell : K)⁻¹ * chiEll * legendre n * eta n +
          (ell : K)⁻¹ * (chiEll * eta n) =
          chiEll * eta n + (ell : K)⁻¹ * chiEll *
            (legendre n * eta n) + (ell : K)⁻¹ * (chiEll * eta n) := by ring
      _ = chiEll * eta n + (ell : K)⁻¹ * (chiEll * eta n) := by rw [hleg]; ring
      _ = chiEll * (1 + (ell : K)⁻¹) * eta n := by ring
  · rw [if_neg hdiv]
    have hleg := hlegendre_not_dvd n hdiv
    calc
      chiEll * eta n + (ell : K)⁻¹ * chiEll * legendre n * eta n + 0 =
          chiEll * eta n + (ell : K)⁻¹ * chiEll *
            (legendre n * eta n) := by ring
      _ = chiEll * eta n + (ell : K)⁻¹ * chiEll * eta n := by rw [hleg]
      _ = chiEll * (1 + (ell : K)⁻¹) * eta n := by ring

/-- Equality of abstract `q`-series follows from coefficientwise equality. -/
theorem qSeries_ext {K : Type*} {f g : QSeries K}
    (h : ∀ n, f n = g n) : f = g :=
  funext h

/-- The uniqueness argument common to the two paper-internal Hecke identities:
once both sides have the required modularity and principal part, grid
uniqueness identifies them. -/
theorem hecke_identity_of_grid_uniqueness
    {V : Type*} {Qualifies : V → Prop} {left right : V}
    (hleft : Qualifies left) (hright : Qualifies right)
    (hunique : ∀ x y, Qualifies x → Qualifies y → x = y) :
    left = right :=
  hunique left right hleft hright

/-- A pointwise commutation check upgrades to equality of operators on the
coefficient model. -/
theorem heckeThetaCommute_of_coefficients
    {K : Type*} {theta hecke : QSeries K → QSeries K}
    (hcoeff : ∀ g n, theta (hecke g) n = hecke (theta g) n) :
    theta ∘ hecke = hecke ∘ theta := by
  funext g
  exact qSeries_ext (hcoeff g)

end CoefficientModels

end SptCM.Analytic
