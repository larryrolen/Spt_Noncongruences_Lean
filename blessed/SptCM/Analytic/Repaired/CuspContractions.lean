module

public import blessed.SptCM.Analytic.Repaired.WeilGenerators
public import Mathlib.Tactic

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Finite Atkin--Lehner cusp calculation

This file implements the four permutations in the paper directly on
`Fin 12`.  The finite eigenvalue computation is independent of the analytic
regularized-pairing bridge.
-/

namespace SptCM.Analytic.Repaired

/-- The four divisors indexing the cusps of squarefree level six. -/
@[expose]
def IsLevelSixDivisor (c : ℕ) : Prop :=
  c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 6

/-- Multiplier description of the simultaneous congruences
`σ_c(r) ≡ -r (mod 2c)` and `σ_c(r) ≡ r (mod 12/c)` at level six. -/
@[expose]
def atkinLehnerMultiplier (c : ℕ) : ℕ :=
  if c = 1 then 1 else if c = 2 then 7 else if c = 3 then 5 else 11

/-- The Atkin--Lehner permutation `σ_c` on `ℤ/12ℤ`. -/
@[expose]
def atkinLehnerSigma (c : ℕ) (r : Fin 12) : Fin 12 :=
  ⟨(atkinLehnerMultiplier c * r.val) % 12, Nat.mod_lt _ (by norm_num)⟩

/-- The sign occurring on the four-component vector: `+,-,-,+` for
`c=1,2,3,6`. -/
@[expose]
def atkinLehnerEigenvalue (c : ℕ) : ℤ :=
  if c = 2 ∨ c = 3 then -1 else 1

/-- The explicit multiplier formula satisfies both simultaneous congruences
from the paper for every divisor of six. -/
theorem atkinLehnerSigma_congruences (c : ℕ) (hc : IsLevelSixDivisor c)
    (r : Fin 12) :
    (atkinLehnerSigma c r).val % (2 * c) =
        ((2 * c - r.val % (2 * c)) % (2 * c)) ∧
      (atkinLehnerSigma c r).val % (12 / c) = r.val % (12 / c) := by
  rcases hc with rfl | rfl | rfl | rfl <;> fin_cases r <;>
    decide

/-- Each `σ_c` is an involution, hence genuinely a permutation. -/
theorem atkinLehnerSigma_involutive (c : ℕ) (hc : IsLevelSixDivisor c) :
    Function.Involutive (atkinLehnerSigma c) := by
  intro r
  rcases hc with rfl | rfl | rfl | rfl <;> fin_cases r <;>
    decide

/-- The paper's finite calculation: the component vector
`e₁-e₅-e₇+e₁₁` has Atkin--Lehner eigenvalue `+1,-1,-1,+1` at the four
level-six cusps. -/
theorem fourComponentVector_atkinLehner_eigenvalue
    (c : ℕ) (hc : IsLevelSixDivisor c) :
    ∀ r : Fin 12,
      chiTwelveResidue (atkinLehnerSigma c r) =
        atkinLehnerEigenvalue c * chiTwelveResidue r := by
  intro r
  rcases hc with rfl | rfl | rfl | rfl <;> fin_cases r <;>
    decide

/-- Function-valued form of the same finite eigenvector calculation. -/
theorem fourComponentVector_atkinLehner (c : ℕ)
    (hc : IsLevelSixDivisor c) (z : ℂ) :
    (fun r => fourComponentVector z (atkinLehnerSigma c r)) =
      fun r => (atkinLehnerEigenvalue c : ℂ) * fourComponentVector z r := by
  funext r
  rw [fourComponentVector, fourComponentVector,
    fourComponentVector_atkinLehner_eigenvalue c hc r]
  push_cast
  ring

/-- Pointwise contraction of the four-component vector against a theta vector. -/
@[expose]
def fourComponentThetaContraction (z : ℂ) (theta : Fin 12 → ℂ) : ℂ :=
  ∑ r, fourComponentVector z r * theta r

/-- The fully internal finite theta-vector contraction.  Permuting the theta
components by `σ_c` multiplies their contraction with `v` by the same
Atkin--Lehner sign.  No regularized-pairing assertion is assumed here. -/
theorem fourComponentThetaContraction_atkinLehner
    (c : ℕ) (hc : IsLevelSixDivisor c) (z : ℂ) (theta : Fin 12 → ℂ) :
    fourComponentThetaContraction z (fun r => theta (atkinLehnerSigma c r)) =
      (atkinLehnerEigenvalue c : ℂ) *
        fourComponentThetaContraction z theta := by
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [fourComponentThetaContraction, fourComponentVector,
      atkinLehnerSigma, atkinLehnerMultiplier, atkinLehnerEigenvalue,
      chiTwelveResidue, Fin.sum_univ_succ] <;> ring

/-- The signed component theta series appearing in Euler's eta identity. -/
@[expose]
def signedComponentThetaSeries {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (theta : Fin 12 → V) : V :=
  ∑ r, (chiTwelveResidue r : ℂ) • theta r

/-- Exact general Euler theta identity in a complex series model.  This is the
standard scalar identity, not a cusp contraction or Weyl-vector assertion. -/
@[expose]
def EtaComponentThetaIdentity {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (theta : Fin 12 → V) (eta : V) : Prop :=
  signedComponentThetaSeries theta = (2 : ℂ) • eta

/-- The componentwise regularized pairing at the cusp indexed by `c`. -/
@[expose]
def regularizedCuspThetaContraction {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (pairing : V →ₗ[ℂ] ℂ) (c : ℕ) (theta : Fin 12 → V) : ℂ :=
  ∑ r, (chiTwelveResidue r : ℂ) * pairing (theta (atkinLehnerSigma c r))

/-- I11, full contraction bridge.  The exact Euler component-theta identity,
linearity of the regularized pairing, and the verified finite Atkin--Lehner
calculation give the four signed scalar pairings.  No cusp-specific
contraction is assumed. -/
theorem regularizedCuspThetaContraction_eq_signed_eta
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (pairing : V →ₗ[ℂ] ℂ) (theta : Fin 12 → V) (eta : V)
    (heta : EtaComponentThetaIdentity theta eta)
    (c : ℕ) (hc : IsLevelSixDivisor c) :
    regularizedCuspThetaContraction pairing c theta =
      (atkinLehnerEigenvalue c : ℂ) * (2 * pairing eta) := by
  have hunpermuted :
      fourComponentThetaContraction 1 (fun r => pairing (theta r)) =
        2 * pairing eta := by
    have hmap := congrArg pairing heta
    simpa [EtaComponentThetaIdentity, signedComponentThetaSeries,
      fourComponentThetaContraction, fourComponentVector,
      map_sum, map_smul] using hmap
  have hfinite :=
    fourComponentThetaContraction_atkinLehner c hc 1
      (fun r => pairing (theta r))
  rw [hunpermuted] at hfinite
  simpa [regularizedCuspThetaContraction, fourComponentThetaContraction,
    fourComponentVector] using hfinite

end SptCM.Analytic.Repaired
