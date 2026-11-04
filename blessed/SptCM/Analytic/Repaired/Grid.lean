module

public import blessed.SptCM.Literature.RolenLiterature
public import blessed.SptCM.Analytic.PaperConstructions

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Repaired modular-grid interface and valid-range theta propagation

The only grid black box in this file is an exact published-grid interface:
existence, the negative principal part, modular qualification, and uniqueness.
Hecke identities are derived from qualification of their two sides.  Theta
support is then derived from those identities, commutation, and a prime-factor
chain whose primes avoid `6 * ℓ`; it is never an interface field.
-/

namespace SptCM.Analytic.Repaired

open SptCM.RolenLiterature
open SptCM.Analytic

/-- The valid index range in Rolen's grid-support proposition. -/
@[expose]
def ValidGridIndex (ℓ m : ℕ) : Prop := Nat.Coprime m (6 * ℓ)

/-- The valid prime step: the Hecke prime is genuinely prime and avoids the
level and the characteristic. -/
@[expose]
def ValidHeckePrime (ℓ p : ℕ) : Prop := p.Prime ∧ Nat.Coprime p (6 * ℓ)

/-- The characteristic-free prime range used by the initial `f`-identity. -/
@[expose]
def ValidLevelPrime (p : ℕ) : Prop := p.Prime ∧ Nat.Coprime p 6

/-- Re-export of the cycle-free, exact literature interface.  This is an
abbreviation, not a second grid theorem or a new caller-chosen family. -/
abbrev AhlgrenKimGridTheorem (K : Type*) [Field K] :=
  SptCM.RolenLiterature.AhlgrenKimGridTheorem K

/-- The canonical grid family supplied by the exact published theorem.
This name is the paper-facing object; all of its mathematical content remains
in `AhlgrenKimGridTheorem`, rather than in an arbitrary choice operator. -/
abbrev gridForm {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (m : ℕ) : QSeries K :=
  G.grid m

/-- The one-index specification satisfied by the fixed member of the
published grid.  Uniqueness remains in `AhlgrenKimGridTheorem`, since it is a
property of the ambient modular-form space rather than of one series. -/
@[expose]
def GenuineGridSpec {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (m : ℕ) : Prop :=
  G.Qualifies m (G.grid m) ∧
    HasGridPrincipalPart G.chi m (G.grid m)

/-- I04 in its exact published range. -/
theorem published_grid_spec
    {K : Type*} [Field K] (G : PublishedMockModularGrid K)
    (m : ℕ) (hm : 1 < m) (hm6 : Nat.Coprime m 6) :
    GenuineGridSpec G m :=
  ⟨G.qualifies_grid m hm hm6, G.principalPart m hm hm6⟩

/-- The published interface gives genuine existence and uniqueness rather than
an arbitrary choice of positive Fourier coefficients. -/
theorem AhlgrenKimGridTheorem.existsUnique
    {K : Type*} [Field K] (G : PublishedMockModularGrid K)
    (m : ℕ) (hm : 1 < m) (hm6 : Nat.Coprime m 6) :
    ∃! g, G.Qualifies m g ∧ HasGridPrincipalPart G.chi m g := by
  refine ⟨G.grid m, ⟨G.qualifies_grid m hm hm6,
    G.principalPart m hm hm6⟩, ?_⟩
  rintro g ⟨hg, hpp⟩
  exact G.unique m hm hm6 g hg hpp

/-- Exact premises obtained by applying the general E3/E4 Hecke and shadow
results and computing principal parts.  They deliberately say that the two
sides qualify; they do not assume the desired equality. -/
structure HeckeQualificationData {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) where
  f : QSeries K
  fHeckeLeft : ℕ → QSeries K
  fHeckeRight : ℕ → QSeries K
  gridHeckeLeft : ℕ → ℕ → QSeries K
  gridHeckeRight : ℕ → ℕ → QSeries K
  f_left_qualifies : ∀ p, ValidLevelPrime p →
    G.Qualifies p (fHeckeLeft p)
  f_right_qualifies : ∀ p, ValidLevelPrime p →
    G.Qualifies p (fHeckeRight p)
  f_left_principalPart : ∀ p, ValidLevelPrime p →
    HasGridPrincipalPart G.chi p (fHeckeLeft p)
  f_right_principalPart : ∀ p, ValidLevelPrime p →
    HasGridPrincipalPart G.chi p (fHeckeRight p)
  grid_left_qualifies : ∀ m p, 1 < m → Nat.Coprime m 6 →
    ValidLevelPrime p → G.Qualifies (m * p) (gridHeckeLeft m p)
  grid_right_qualifies : ∀ m p, 1 < m → Nat.Coprime m 6 →
    ValidLevelPrime p → G.Qualifies (m * p) (gridHeckeRight m p)
  grid_left_principalPart : ∀ m p, 1 < m → Nat.Coprime m 6 →
    ValidLevelPrime p →
      HasGridPrincipalPart G.chi (m * p) (gridHeckeLeft m p)
  grid_right_principalPart : ∀ m p, 1 < m → Nat.Coprime m 6 →
    ValidLevelPrime p →
      HasGridPrincipalPart G.chi (m * p) (gridHeckeRight m p)

/-- The source-faithful pair of Hecke identities, with every quantifier
restricted to the range in which the qualification calculations apply. -/
@[expose]
def HeckeIdentitySpec {K : Type*} [Field K]
    (G : PublishedMockModularGrid K)
    (D : HeckeQualificationData G) : Prop :=
  (∀ p, ValidLevelPrime p →
    D.fHeckeLeft p = D.fHeckeRight p) ∧
  (∀ m p, 1 < m → Nat.Coprime m 6 → ValidLevelPrime p →
      D.gridHeckeLeft m p = D.gridHeckeRight m p)

/-- The `f`-Hecke identity is a checked uniqueness deduction from exact
qualification and principal-part computations. -/
theorem f_hecke_identity
    {K : Type*} [Field K] (G : PublishedMockModularGrid K)
    (D : HeckeQualificationData G) (p : ℕ)
    (hp : ValidLevelPrime p) :
    D.fHeckeLeft p = D.fHeckeRight p := by
  have hp1 : 1 < p := hp.1.one_lt
  have hp6 : Nat.Coprime p 6 := hp.2
  exact (G.unique p hp1 hp6 (D.fHeckeLeft p)
    (D.f_left_qualifies p hp) (D.f_left_principalPart p hp)).trans
      (G.unique p hp1 hp6 (D.fHeckeRight p)
        (D.f_right_qualifies p hp) (D.f_right_principalPart p hp)).symm

/-- The grid Hecke recurrence is likewise derived only in the range
`(m,6ℓ)=1`, `p ∤ 6ℓ`. -/
theorem grid_hecke_identity
    {K : Type*} [Field K] (G : PublishedMockModularGrid K)
    (D : HeckeQualificationData G) (m p : ℕ)
    (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (hp : ValidLevelPrime p) :
    D.gridHeckeLeft m p = D.gridHeckeRight m p := by
  have hmp : 1 < m * p :=
    Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m hp.1.pos)
  have hcop : Nat.Coprime (m * p) 6 := hm6.mul_left hp.2
  exact (G.unique (m * p) hmp hcop (D.gridHeckeLeft m p)
    (D.grid_left_qualifies m p hm hm6 hp)
    (D.grid_left_principalPart m p hm hm6 hp)).trans
      (G.unique (m * p) hmp hcop (D.gridHeckeRight m p)
        (D.grid_right_qualifies m p hm hm6 hp)
        (D.grid_right_principalPart m p hm hm6 hp)).symm

/-- I05 bundled from the two uniqueness deductions; the specification itself
is not a field of either external interface. -/
theorem published_hecke_identities
    {K : Type*} [Field K] (G : PublishedMockModularGrid K)
    (D : HeckeQualificationData G) :
    HeckeIdentitySpec G D := by
  constructor
  · exact fun p hp => f_hecke_identity G D p hp
  · exact fun m p hm hm6 hp =>
      grid_hecke_identity G D m p hm hm6 hp

/-- A prime grid form inherits theta support from the `f`-Hecke identity.
The Hecke identity itself is not an input of the published grid theorem. -/
theorem prime_grid_theta_support
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta hecke : V →ₗ[K] V} {epsilon a c : K} {f Gp : V}
    (hc : c ≠ 0) (hcomm : theta.comp hecke = hecke.comp theta)
    (hf : AhlgrenKimThetaCycleInput theta epsilon f)
    (hidentity : hecke f - a • f = c • Gp) :
    IsThetaEigen theta epsilon Gp :=
  thetaEigen_grid_of_f_hecke_identity hc hcomm hf hidentity

/-- A valid grid recurrence step preserves theta support.  The remainder must
be proved to be supported from earlier grid indices; support of `G_{mp}` is
not assumed. -/
theorem grid_theta_support_step
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {theta hecke : V →ₗ[K] V} {epsilon c : K}
    {Gm Gmp remainder : V}
    (hc : c ≠ 0) (hcomm : theta.comp hecke = hecke.comp theta)
    (hm : IsThetaEigen theta epsilon Gm)
    (hrem : IsThetaEigen theta epsilon remainder)
    (hrec : hecke Gm = c • Gmp + remainder) :
    IsThetaEigen theta epsilon Gmp :=
  thetaEigen_grid_recurrence_step hc hcomm hm hrem hrec

/-- Restricted prime-factor induction.  Every step carries the exact
coprimality hypotheses; in particular a factor `p = ℓ` is impossible. -/
theorem grid_theta_support_of_primeFactorChain
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ℓ : ℕ) (theta : V →ₗ[K] V) (epsilon : K) (G : ℕ → V)
    (chain : List ℕ)
    (hvalid : ∀ p ∈ chain, ValidHeckePrime ℓ p)
    (hsuffix : ∀ ps, ps <:+ chain → ValidGridIndex ℓ ps.prod)
    (hbase : IsThetaEigen theta epsilon (G 1))
    (hstep : ∀ m p, ValidGridIndex ℓ m → ValidHeckePrime ℓ p →
      IsThetaEigen theta epsilon (G m) →
        IsThetaEigen theta epsilon (G (m * p))) :
    IsThetaEigen theta epsilon (G chain.prod) := by
  induction chain with
  | nil => simpa using hbase
  | cons p ps ih =>
      have hp : ValidHeckePrime ℓ p := hvalid p (by simp)
      have htail : ∀ q ∈ ps, ValidHeckePrime ℓ q := by
        intro q hq
        exact hvalid q (by simp [hq])
      have htailSuffix : ∀ qs, qs <:+ ps → ValidGridIndex ℓ qs.prod := by
        intro qs hqs
        exact hsuffix qs (hqs.trans (by simp))
      have hps : IsThetaEigen theta epsilon (G ps.prod) :=
        ih htail htailSuffix
      have hcops : ValidGridIndex ℓ ps.prod := hsuffix ps (by simp)
      simpa [List.prod_cons, mul_comm] using hstep ps.prod p hcops hp hps

end SptCM.Analytic.Repaired
