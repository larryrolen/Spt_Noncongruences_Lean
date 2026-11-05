module

public import Mathlib

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}


/-!
# Transcendence from a Laurent pole

A Laurent series with leading term `X⁻¹` cannot be algebraic over its
coefficient field: the `X`-adic valuation is trivial on constants, while the
series has nontrivial valuation.
-/

namespace SptCM.Repair

/-- A Laurent series whose coefficient at `-1` is one (and which has no terms
below `-1`) is transcendental over its coefficient field. -/
theorem laurentSeries_transcendental_of_simple_pole
    {K : Type*} [Field K] (t : LaurentSeries K)
    (hcoeff : t.coeff (-1) = 1)
    (_hbelow : ∀ z : ℤ, z < -1 → t.coeff z = 0) :
    Transcendental K t := by
  letI : Valuation.IsTrivialOn K (Valued.v : Valuation (LaurentSeries K) _) :=
    Valuation.IsTrivialOn.of_le_one Valued.v fun a =>
      (LaurentSeries.val_le_one_iff_eq_coe K _).mpr
        ⟨PowerSeries.C a, by
          rw [LaurentSeries.algebraMap_apply]
          exact HahnSeries.ofPowerSeries_C a⟩
  apply Valuation.transcendental_of_ne_one (v := (Valued.v : Valuation (LaurentSeries K) _)) K t
  · intro ht
    have hz : t.coeff (-1) = 0 := ht ▸ HahnSeries.coeff_zero
    exact one_ne_zero (hcoeff.symm.trans hz)
  · intro hv
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe K t).mp (le_of_eq hv)
    have hz : (F : LaurentSeries K).coeff (-1) = 0 :=
      (PowerSeries.coeff_coe (f := F) (-1)).trans (if_pos (Int.negSucc_lt_zero 0))
    exact zero_ne_one (hz.symm.trans
      ((congrArg (fun f : LaurentSeries K => f.coeff (-1)) hF).trans hcoeff))

end SptCM.Repair
