module

public import blessed.SptCM.Analytic.Repaired.Grid

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Identification of the published grid normalization

This module performs the paper-specific comparison between the exact
Ahlgren--Kim grid interface and the coefficient convention used throughout
this development.  It imports no theta-support, Hecke, or duality conclusion.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic
open SptCM.RolenLiterature

/-- The complete normalization agreement needed to identify the exact
published grid with the fixed family `G_m` used in the paper.

The qualification predicate retains the published multiplier convention.  The
coefficient formula makes explicit the numerator-indexed exponents, the
character, both principal-part signs, and the coprime range. -/
@[expose]
def PublishedGridNormalizationAgreement
    {K : Type*} [Field K] (G : PublishedMockModularGrid K) : Prop :=
  gridForm G 1 = 0 ∧
    ∀ m, 1 < m → Nat.Coprime m 6 →
      G.Qualifies m (gridForm G m) ∧
        ∀ r : ℤ, r < 0 →
          gridForm G m r =
            if r = -(m : ℤ) ^ 2 then 1
            else if r = -1 then -G.chi m else 0

/-- I04: the data-bearing Ahlgren--Kim theorem has exactly the normalization
used by the fixed paper family.  This is a direct componentwise identification,
not an assumed semantic-model field. -/
theorem published_grid_normalization_agreement
    {K : Type*} [Field K] (G : PublishedMockModularGrid K) :
    PublishedGridNormalizationAgreement G := by
  refine ⟨G.grid_one, ?_⟩
  intro m hm hm6
  refine ⟨G.qualifies_grid m hm hm6, ?_⟩
  exact G.principalPart m hm hm6

end SptCM.Analytic.Repaired
