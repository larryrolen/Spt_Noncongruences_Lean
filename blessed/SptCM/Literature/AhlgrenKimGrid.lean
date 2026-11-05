module

public import blessed.SptCM.Analytic.ThetaHecke
public import blessed.SptCM.Analytic.ChiTwelve

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Exact Ahlgren--Kim modular-grid literature interface

This cycle-free module records the data and theorem actually supplied by the
published modular-grid result.  It deliberately contains no Hecke recurrence,
theta-support assertion, coefficient vanishing, or duality conclusion.
-/

namespace SptCM.RolenLiterature

open SptCM.Analytic

/-- Exact E4 boundary for the published Ahlgren--Kim modular grid.

The record carries the fixed grid, its multiplier, the modular qualification,
the two-term negative principal part in the published range, and uniqueness in
that same range.  Thus positive Fourier coefficients are data of the published
family rather than a freely chosen tail. -/
structure AhlgrenKimGridTheorem (K : Type*) [Field K] where
  chi : ℕ → K
  chi_eq_chi12 : ∀ m, chi m = (SptCM.Analytic.chi12 m : K)
  grid : ℕ → QSeries K
  Qualifies : ℕ → QSeries K → Prop
  grid_one : grid 1 = 0
  qualifies_grid : ∀ m, 1 < m → Nat.Coprime m 6 → Qualifies m (grid m)
  principalPart : ∀ m, 1 < m → Nat.Coprime m 6 →
    HasGridPrincipalPart chi m (grid m)
  unique : ∀ m, 1 < m → Nat.Coprime m 6 → ∀ g,
    Qualifies m g → HasGridPrincipalPart chi m g → g = grid m

/-- The exact data-bearing published-grid result, rather than an opaque
proposition saying merely that some grid has been published. -/
abbrev PublishedMockModularGrid (K : Type*) [Field K] :=
  AhlgrenKimGridTheorem K

end SptCM.RolenLiterature
