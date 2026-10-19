import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# General squarefree-level cusp classification interface

This module defines the actual cusp orbit set for `Γ₀(N)` and records the
standard general squarefree-level classification.  It contains no
level-six conclusion.
-/

namespace SptCM.RolenLiterature

open CongruenceSubgroup

/-- The Möbius action of the integral congruence subgroup on the rational
projective line. -/
local instance gammaZeroAction (N : ℕ) :
    MulAction (Gamma0 N) (OnePoint ℚ) :=
  MulAction.compHom (OnePoint ℚ)
    ((Matrix.SpecialLinearGroup.mapGL ℚ).comp (Gamma0 N).subtype)

/-- Cusps of `X₀(N)`, represented as `Γ₀(N)`-orbits in `ℙ¹(ℚ)`. -/
abbrev GammaZeroCusp (N : ℕ) :=
  MulAction.orbitRel.Quotient (Gamma0 N) (OnePoint ℚ)

/-- The positive divisors used in the squarefree-level cusp classification. -/
abbrev LevelDivisor (N : ℕ) := {d : ℕ // d ∣ N}

/-- The standard representative attached to a divisor `d ∣ N`. -/
def squarefreeCuspPoint (N : ℕ) (d : LevelDivisor N) : OnePoint ℚ :=
  if d.1 = 1 then (0 : ℚ)
  else if d.1 = N then OnePoint.infty
  else ((1 / (d.1 : ℚ) : ℚ) : OnePoint ℚ)

/-- The corresponding orbit class on `X₀(N)`. -/
def squarefreeCuspRepresentative (N : ℕ) (d : LevelDivisor N) :
    GammaZeroCusp N :=
  Quotient.mk'' (squarefreeCuspPoint N d)

/-- General E4/E11 squarefree-level cusp classification. -/
def SquarefreeGammaZeroCuspClassification : Prop :=
  ∀ (N : ℕ), N ≠ 0 → Squarefree N →
    Function.Bijective (squarefreeCuspRepresentative N)

end SptCM.RolenLiterature
