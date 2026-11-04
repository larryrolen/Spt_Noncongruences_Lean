module

public import blessed.SptCM.Analytic.Repaired.AuxiliaryForms
public import blessed.SptCM.Analytic.Repaired.WeilGenerators

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Exact Fourier data of the four-component Borcherds input

This file proves the coefficient statement behind I10 directly from the
triangular normalization of the actual auxiliary form.  It does not assume a
Borcherds admissibility predicate or a Weil transformation law.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic

/-- The integral twelve-component coefficient function `H v`, where
`v = e₁ - e₅ - e₇ + e₁₁`. -/
@[expose]
def fourComponentHSeries (H : HForm ℤ) : ℤ → Fin 12 → ℤ :=
  fun r s => H r * chiTwelveResidue s

/-- Exact coefficient content needed from the four-component input: zero
constant coefficient, and a single integral negative index `-n` whose vector
is `e₁-e₅-e₇+e₁₁`. -/
@[expose]
def HasFourComponentFourierData (n : ℕ) (V : ℤ → Fin 12 → ℤ) : Prop :=
  (∀ s, V 0 s = 0) ∧
    ∀ r : ℤ, r < 0 → ∀ s,
      V r s = if r = -(n : ℤ) then chiTwelveResidue s else 0

/-- Any scalar auxiliary series with the paper's normalization has the exact
four-component constant term and integral principal part. -/
theorem fourComponentHSeries_fourierData_of_normalization
    (n : ℕ) (hn : 0 < n) (a : ℤ) (H : HForm ℤ)
    (hH : HasHnNormalization n a H) :
    HasFourComponentFourierData n (fourComponentHSeries H) := by
  constructor
  · intro s
    have hzero : H 0 = 0 := hH.2.2 0 (by omega) (by omega) (by omega)
    simp [fourComponentHSeries, hzero]
  · intro r hr s
    by_cases hrn : r = -(n : ℤ)
    · subst r
      simp [fourComponentHSeries, hH.1]
    · have hr1 : r ≠ 1 := by omega
      have hz : H r = 0 := hH.2.2 r (by omega) hrn hr1
      simp [fourComponentHSeries, hrn, hz]

/-- I10's Fourier calculation for the actual triangularly constructed
`H_n = η P_n(j)`: its four-component form has zero constant term and exactly
the required integral principal part. -/
theorem auxiliaryHn_fourComponent_fourierData
    {Form : Type*} (E : EtaJPowerBasis Form)
    (k : ℕ) (hk : 0 < k) (a : ℤ) :
    HasFourComponentFourierData (24 * k - 1)
      (fourComponentHSeries (auxiliaryHn E k a)) := by
  apply fourComponentHSeries_fourierData_of_normalization
    (24 * k - 1) (by omega) a (auxiliaryHn E k a)
  exact auxiliaryHn_normalization E k hk a


/-- Integral vector Fourier series attached to an actual four-component
input.  The finite sign vector is fixed by the type of input. -/
@[expose]
def FourComponentInput.vectorSeries {Form : Type*}
    (F : FourComponentInput Form) : ℤ → Fin 12 → ℤ :=
  fourComponentHSeries F.scalarSeries

/-- Fourier-data theorem stated on the very same actual input used in the
Weil-generator calculation. -/
theorem auxiliaryFourComponentInput_fourierData
    {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form)
    (k : ℕ) (hk : 0 < k) (a : ℤ) :
    HasFourComponentFourierData (24 * k - 1)
      (auxiliaryFourComponentInput E k a).vectorSeries := by
  exact auxiliaryHn_fourComponent_fourierData
    E.toEtaJPowerBasis k hk a

end SptCM.Analytic.Repaired
