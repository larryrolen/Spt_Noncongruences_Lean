import blessed.SptCM.Analytic.PaperCoefficientModels
import blessed.SptCM.Interfaces

/-!
# Prime and discriminant ranges for the analytic obstruction

The analytic data used in the obstruction are only requested at primes at
least five and at admissible discriminants.  This rules out the zero-ring and
small-characteristic cases before any nonvanishing field is introduced.
-/

namespace SptCM.Repair

/-- The actual prime/discriminant range in which the analytic obstruction is
used. -/
def AnalyticAdmissible (ℓ n : ℕ) : Prop :=
  ℓ.Prime ∧ 5 ≤ ℓ ∧ SptCM.Admissible ℓ n

namespace AnalyticAdmissible

 theorem prime {ℓ n : ℕ} (h : AnalyticAdmissible ℓ n) : ℓ.Prime := h.1
 theorem five_le {ℓ n : ℕ} (h : AnalyticAdmissible ℓ n) : 5 ≤ ℓ := h.2.1
 theorem admissible {ℓ n : ℕ} (h : AnalyticAdmissible ℓ n) :
    SptCM.Admissible ℓ n := h.2.2

end AnalyticAdmissible

/-- Characteristic one is excluded before analytic data are requested. -/
theorem not_analyticAdmissible_one (n : ℕ) : ¬ AnalyticAdmissible 1 n := by
  simp [AnalyticAdmissible]

/-- Characteristic three is excluded before division by 24 or Euler's
criterion is used. -/
theorem not_analyticAdmissible_three (n : ℕ) : ¬ AnalyticAdmissible 3 n := by
  simp [AnalyticAdmissible]

/-- A concrete nonprincipality predicate for an integer-valued character
modulo `p`: it takes a value other than one at some unit.  This replaces an
uninterpreted caller-chosen label. -/
def IsNonprincipalModCharacter
    (p : ℕ) (χ : ℤ → ℤ) : Prop :=
  ∃ a : ℤ, ¬(p : ℤ) ∣ a ∧ χ a ≠ 1

/-- For the Legendre character, a quadratic nonresidue is precisely a
nonprincipality witness. -/
theorem legendre_isNonprincipal_of_neg_one
    (p : ℕ) [Fact p.Prime]
    (h : ∃ a : ℤ, legendreSym p a = -1) :
    IsNonprincipalModCharacter p (legendreSym p) := by
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_, by omega⟩
  intro hd
  have hz : (a : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have := (legendreSym.eq_zero_iff p a).2 hz
  omega

/-- In the actual range, 24 is nonzero modulo `ℓ`. -/
private theorem twentyFour_ne_zero_of_prime_five
    (ℓ : ℕ) (hprime : ℓ.Prime) (hfive : 5 ≤ ℓ) :
    (24 : ZMod ℓ) ≠ 0 := by
  change ((24 : ℕ) : ZMod ℓ) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have hd' : ℓ ∣ 3 * 2 ^ 3 := by norm_num at hd ⊢; exact hd
  rcases hprime.dvd_mul.mp hd' with hthree | height
  · have : ℓ ≤ 3 := Nat.le_of_dvd (by norm_num) hthree
    omega
  · have htwo : ℓ ∣ 2 := hprime.dvd_of_dvd_pow height
    have : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
    omega

theorem twentyFour_ne_zero
    {ℓ n : ℕ} (hrange : AnalyticAdmissible ℓ n) :
    (24 : ZMod ℓ) ≠ 0 :=
  twentyFour_ne_zero_of_prime_five ℓ hrange.prime hrange.five_le

/-- The corrected range simultaneously excludes the two regression cases and
makes the normalization denominator nonzero. -/
theorem analyticAdmissible_sound_range
    {ℓ n : ℕ} (hrange : AnalyticAdmissible ℓ n) :
    ℓ ≠ 1 ∧ ℓ ≠ 3 ∧ (24 : ZMod ℓ) ≠ 0 := by
  refine ⟨?_, ?_, twentyFour_ne_zero hrange⟩
  · intro h
    subst h
    exact not_analyticAdmissible_one n hrange
  · intro h
    subst h
    exact not_analyticAdmissible_three n hrange

/-- Euler's criterion gives exactly the mismatch used in the inert-coefficient
argument, once the prime is in the paper's range. -/
theorem eulerInertMismatch_of_five_le
    (ℓ : ℕ) [Fact ℓ.Prime] (hfive : 5 ≤ ℓ) :
    SptCM.Analytic.EulerInertMismatchInput ℓ := by
  intro r hinert heq
  have hp : ℓ.Prime := Fact.out
  obtain ⟨k, hkodd⟩ := hp.odd_of_ne_two (by omega : ℓ ≠ 2)
  have hk : ℓ / 2 = (ℓ - 1) / 2 := by omega
  have h24 : (24 : ZMod ℓ) ≠ 0 :=
    twentyFour_ne_zero_of_prime_five ℓ hp hfive
  have hleg24 : (legendreSym ℓ (24 : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [legendreSym.eq_pow, hk]
    exact pow_ne_zero _ (by exact_mod_cast h24)
  have hpowr := legendreSym.eq_pow ℓ r
  have hpow24 := legendreSym.eq_pow ℓ (24 : ℤ)
  rw [hk] at hpowr hpow24
  have hratio :
      (legendreSym ℓ r : ZMod ℓ) / (legendreSym ℓ (24 : ℤ) : ZMod ℓ) =
        (legendreSym ℓ (-24 : ℤ) : ZMod ℓ) := by
    rw [hpowr, hpow24]
    simpa [div_pow, SptCM.Analytic.thetaCycleEigenvalue] using heq
  have hmul :
      legendreSym ℓ (-24) * legendreSym ℓ r =
        -legendreSym ℓ (24 : ℤ) := by
    calc
      legendreSym ℓ (-24) * legendreSym ℓ r =
          legendreSym ℓ ((-24) * r) := (legendreSym.mul ℓ _ _).symm
      _ = legendreSym ℓ ((-r) * 24) := by ring_nf
      _ = legendreSym ℓ (-r) * legendreSym ℓ 24 :=
        legendreSym.mul ℓ _ _
      _ = -legendreSym ℓ 24 := by rw [hinert]; ring
  have hcast :
      (legendreSym ℓ (-24 : ℤ) : ZMod ℓ) *
          (legendreSym ℓ r : ZMod ℓ) =
        -(legendreSym ℓ (24 : ℤ) : ZMod ℓ) := by
    have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hmul
    push_cast at this
    exact this
  have hnegarg : ((-24 : ℤ) : ZMod ℓ) ≠ 0 := by
    simpa using (neg_ne_zero.mpr (by exact_mod_cast h24))
  have hvalues := legendreSym.eq_one_or_neg_one ℓ (a := -24) hnegarg
  have htwo : (2 : ZMod ℓ) ≠ 0 := by
    change ((2 : ℕ) : ZMod ℓ) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  rcases hvalues with hvalue | hvalue
  · have ha : (legendreSym ℓ (-24 : ℤ) : ZMod ℓ) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hvalue
      simpa using this
    rw [ha] at hratio hcast
    field_simp [hleg24] at hratio
    rw [hratio] at hcast
    apply hleg24
    apply (mul_eq_zero.mp (show (2 : ZMod ℓ) *
      (legendreSym ℓ (24 : ℤ) : ZMod ℓ) = 0 by
        linear_combination hcast)).resolve_left htwo
  · have ha : (legendreSym ℓ (-24 : ℤ) : ZMod ℓ) = -1 := by
      have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hvalue
      simpa using this
    rw [ha] at hratio hcast
    field_simp [hleg24] at hratio
    rw [hratio] at hcast
    apply hleg24
    apply (mul_eq_zero.mp (show (2 : ZMod ℓ) *
      (legendreSym ℓ (24 : ℤ) : ZMod ℓ) = 0 by
        linear_combination hcast)).resolve_left htwo

end SptCM.Repair
