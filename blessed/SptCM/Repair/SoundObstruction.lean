import blessed.SptCM.Repair.AdmissibleRange
import blessed.SptCM.Repair.GridSupport
import blessed.SptCM.Repair.SignedExponent
import blessed.SptCM.Repair.LaurentHauptmodul
import blessed.SptCM.CM.Borcherds
import blessed.SptCM.Analytic.Repaired.EulerProducts

/-!
# Sound local analytic obstruction interface

This local structure replaces universal fields over arbitrary natural
characteristics by data indexed by one admissible prime/discriminant pair.
Signed exponents and the Euler mismatch are derived rather than postulated.
-/

namespace SptCM.Repair

/-- The diagonal theta power as a linear map on coefficient series. -/
def thetaPowerLinearMap (ℓ k : ℕ) [Fact ℓ.Prime] :
    SptCM.Analytic.QSeries (ZMod ℓ) →ₗ[ZMod ℓ]
      SptCM.Analytic.QSeries (ZMod ℓ) where
  toFun := SptCM.Analytic.thetaPowerSeriesOp ℓ k
  map_add' := by
    intro f g
    funext r
    simp only [SptCM.Analytic.thetaPowerSeriesOp_apply, Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext r
    simp only [SptCM.Analytic.thetaPowerSeriesOp_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- P0-repaired analytic data at one admissible pair.  The Euler products are
not fields: they are constructed canonically from `H` below.  The remaining
grid construction is an honest P1 obligation, and no field is requested at
`ℓ = 1`, `ℓ = 3`, an inadmissible discriminant, or the forbidden factor
`p = ℓ`. -/
structure SoundAnalyticObstructionData
    (ℓ n : ℕ) [Fact ℓ.Prime] (hrange : AnalyticAdmissible ℓ n) where
  H : ℤ → ℤ
  chi : ℕ → ZMod ℓ
  grid : ℕ → SptCM.Analytic.QSeries (ZMod ℓ)
  gridTheta : RestrictedGridThetaData (ZMod ℓ)
    (SptCM.Analytic.QSeries (ZMod ℓ)) ℓ
    (thetaPowerLinearMap ℓ ((ℓ - 1) / 2))
    (SptCM.Analytic.thetaCycleEigenvalue ℓ) grid
  hauptmodul : LaurentHauptmodulData ℓ n hrange

/-- The numerator is the canonical stabilized product, not caller data. -/
noncomputable def SoundAnalyticObstructionData.numerator
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    PowerSeries (ZMod ℓ) :=
  eulerProductPlus d.H

/-- The denominator is likewise the canonical stabilized product. -/
noncomputable def SoundAnalyticObstructionData.denominator
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    PowerSeries (ZMod ℓ) :=
  eulerProductMinus d.H

theorem SoundAnalyticObstructionData.numeratorProduct
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    SptCM.IsStabilizedEulerProduct d.numerator id
      (positiveEulerExponent d.H) :=
  (eulerProducts_spec (R := ZMod ℓ) d.H).1

theorem SoundAnalyticObstructionData.denominatorProduct
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    SptCM.IsStabilizedEulerProduct d.denominator id
      (negativeEulerExponent d.H) :=
  (eulerProducts_spec (R := ZMod ℓ) d.H).2.1

theorem SoundAnalyticObstructionData.denominator_ne_zero
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
  (d : SoundAnalyticObstructionData ℓ n hrange) :
    d.denominator ≠ 0 :=
  (eulerProducts_spec (R := ZMod ℓ) d.H).2.2.2.2.2.1.ne_zero

/-- The exact signed exponent identity needed after reduction modulo `ℓ`. -/
theorem SoundAnalyticObstructionData.exponentIdentity
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) (m : ℕ) :
    (positiveEulerExponent d.H m : ZMod ℓ) -
      (negativeEulerExponent d.H m : ZMod ℓ) =
        (SptCM.Analytic.chi12 (m : ℤ) * d.H ((m : ℤ) ^ 2) : ZMod ℓ) := by
  simpa [signedEulerExponent] using
    positive_sub_negativeEulerExponent_zmod ℓ d.H m

/-- The one-sidedness of the numerator/denominator exponent split is derived
from the signed integer exponent. -/
theorem SoundAnalyticObstructionData.oneSided
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) (m : ℕ) :
    positiveEulerExponent d.H m = 0 ∨
      negativeEulerExponent d.H m = 0 :=
  positive_or_negativeEulerExponent_eq_zero d.H m

/-- Euler mismatch is a theorem in the local range, not an unrestricted
structure field. -/
theorem SoundAnalyticObstructionData.eulerMismatch
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (_d : SoundAnalyticObstructionData ℓ n hrange) :
    SptCM.Analytic.EulerInertMismatchInput ℓ := by
  exact eulerInertMismatch_of_five_le ℓ hrange.five_le

/-- The corrected Laurent Hauptmodul has injective polynomial substitution. -/
theorem SoundAnalyticObstructionData.substitution_injective
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    Function.Injective
      (fun P : Polynomial (ZMod ℓ) => Polynomial.aeval d.hauptmodul.t P) :=
  d.hauptmodul.substitution_injective

/-- Its Laurent derivative is nonzero as a consequence of the `q⁻¹`
principal coefficient. -/
theorem SoundAnalyticObstructionData.derivative_ne_zero
    {ℓ n : ℕ} [Fact ℓ.Prime] {hrange : AnalyticAdmissible ℓ n}
    (d : SoundAnalyticObstructionData ℓ n hrange) :
    LaurentSeries.derivative (ZMod ℓ) d.hauptmodul.t ≠ 0 :=
  d.hauptmodul.derivative_ne_zero

end SptCM.Repair
