module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.RingTheory.Valuation.Integers

public section


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
          simp⟩
  apply Valuation.transcendental_of_ne_one (v := (Valued.v : Valuation (LaurentSeries K) _)) K t
  · intro ht
    have hc := congrArg (fun f : LaurentSeries K => f.coeff (-1)) ht
    simp [hcoeff] at hc
  · intro hv
    have hle : Valued.v t ≤ 1 := le_of_eq hv
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe K t).mp hle
    have hc := congrArg (fun f : LaurentSeries K => f.coeff (-1)) hF
    rw [PowerSeries.coeff_coe] at hc
    simpa [hcoeff] using hc

end SptCM.Repair
