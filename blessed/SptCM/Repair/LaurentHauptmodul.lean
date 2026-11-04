module

public import blessed.SptCM.Repair.AdmissibleRange
public import blessed.SptCM.Repair.LaurentTranscendence

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Laurent-series Hauptmodul interface

The level-six Hauptmodul begins with `q⁻¹`, so it is represented directly as a
Laurent series rather than incorrectly as a power series.
-/

namespace SptCM.Repair

/-- The principal part `t(q) = q⁻¹ - 5 + O(q)` of the level-six Hauptmodul. -/
@[expose]
def HasHauptmodulPrincipalPart {K : Type*} [Ring K]
    (t : LaurentSeries K) : Prop :=
  t.coeff (-1) = 1 ∧ t.coeff 0 = -5 ∧
    ∀ z : ℤ, z < -1 → t.coeff z = 0

/-- The reciprocal coordinate has expansion `u = q + O(q²)`. -/
@[expose]
def HasReciprocalHauptmodulExpansion {K : Type*} [Ring K]
    (u : PowerSeries K) : Prop :=
  PowerSeries.coeff 0 u = 0 ∧ PowerSeries.coeff 1 u = 1

/-- A range-correct Laurent-series interface for the Hauptmodul.  The
nonvanishing and substitution properties are requested only at an admissible
prime/discriminant pair. -/
structure LaurentHauptmodulData (ℓ n : ℕ)
    (hrange : AnalyticAdmissible ℓ n) where
  t : LaurentSeries (ZMod ℓ)
  principalPart : HasHauptmodulPrincipalPart t

/-- Optional reciprocal presentation of the same Hauptmodul.  The equality is
stated after embedding the power series into Laurent series, so no power
series is incorrectly asked to contain the pole of `t`. -/
structure LaurentReciprocalHauptmodulData (ℓ n : ℕ)
    [Fact ℓ.Prime] (hrange : AnalyticAdmissible ℓ n)
    extends LaurentHauptmodulData ℓ n hrange where
  u : PowerSeries (ZMod ℓ)
  uExpansion : HasReciprocalHauptmodulExpansion u
  reciprocal :
    (u : LaurentSeries (ZMod ℓ)) = t⁻¹

/-- The principal coefficient alone proves that the Laurent Hauptmodul is
nonzero. -/
theorem hauptmodul_ne_zero {K : Type*} [Nontrivial K] [Ring K]
    {t : LaurentSeries K} (h : HasHauptmodulPrincipalPart t) : t ≠ 0 := by
  intro ht
  have hc := congrArg (fun f : LaurentSeries K => f.coeff (-1)) ht
  simp [h.1] at hc

/-- The pole coefficient also forces the formal Laurent derivative to be
nonzero: its coefficient at `q⁻²` is `-1`. -/
theorem hauptmodul_derivative_ne_zero
    {K : Type*} [Nontrivial K] [CommRing K]
    {t : LaurentSeries K} (h : HasHauptmodulPrincipalPart t) :
    LaurentSeries.derivative K t ≠ 0 := by
  intro ht
  have hc := congrArg
    (fun f : LaurentSeries K => f.coeff (-2)) ht
  simp [LaurentSeries.derivative, h.1] at hc

/-- The Hauptmodul's prescribed pole makes it transcendental over the
coefficient field; this need not be stored as additional interface data. -/
theorem LaurentHauptmodulData.transcendental
    {ℓ n : ℕ} {hrange : AnalyticAdmissible ℓ n}
    (d : LaurentHauptmodulData ℓ n hrange) :
    Transcendental (ZMod ℓ) d.t := by
  letI : Fact ℓ.Prime := ⟨hrange.prime⟩
  exact laurentSeries_transcendental_of_simple_pole d.t
    d.principalPart.1 d.principalPart.2.2

/-- Transcendence gives injective polynomial substitution into Laurent
series, exactly as required by the Wronskian argument. -/
theorem LaurentHauptmodulData.substitution_injective
    {ℓ n : ℕ} {hrange : AnalyticAdmissible ℓ n}
    (d : LaurentHauptmodulData ℓ n hrange) :
    Function.Injective
      (fun P : Polynomial (ZMod ℓ) => Polynomial.aeval d.t P) :=
  transcendental_iff_injective.mp d.transcendental

/-- Nonzero derivative is a theorem of the Laurent principal part, not a
universally quantified field at invalid characteristics. -/
theorem LaurentHauptmodulData.derivative_ne_zero
    {ℓ n : ℕ} {hrange : AnalyticAdmissible ℓ n}
    (d : LaurentHauptmodulData ℓ n hrange) :
    LaurentSeries.derivative (ZMod ℓ) d.t ≠ 0 := by
  letI : Fact ℓ.Prime := ⟨hrange.prime⟩
  exact hauptmodul_derivative_ne_zero d.principalPart

end SptCM.Repair
