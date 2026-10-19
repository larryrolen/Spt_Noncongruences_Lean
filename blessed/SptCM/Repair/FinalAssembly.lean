import blessed.SptCM.Repair.AndrewsCongruences
import blessed.SptCM.Repair.TrevinoBridge

/-!
# Final cutoff assembly with the exact E1 and E2 statements

This module isolates the last purely logical step of Rolen's classification.
The only remaining premise, `hlarge`, is intentionally the high-prime
contradiction that must be produced by the repaired analytic and CM chains;
it is not placed in the literature record.
-/

namespace SptCM.Repair

open SptCM.RolenLiterature

/-- The exact public mathematical statement of Rolen's Theorem 1.1. -/
def RolenClassificationStatement : Prop :=
  ∀ ℓ : ℕ, CanonicalCongruencePrime ℓ ↔
    ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13

/-- The final high-prime contradiction, separated from both analytic and CM
constructions.  Unlike `hlarge` in the public assembly theorem below, this
does not assume the desired exclusion: E10 constructs the discriminant, and
the two independently proved Wronskian conclusions contradict each other. -/
theorem large_exclusion_of_wronskian_contradiction
    (hE10 : E10TrevinoCorrected)
    (W : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hzero : ∀ (ℓ n : ℕ) [Fact ℓ.Prime],
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
      W ℓ n = 0)
    (hnonzero : ∀ (ℓ n : ℕ) [Fact ℓ.Prime],
      Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
      (n + 1) ^ 2 < 24 * ℓ →
      0 < 2 * SptCM.negativeClassNumber n →
      2 * SptCM.negativeClassNumber n < ℓ →
      W ℓ n ≠ 0)
    (ℓ : ℕ) (hprime : ℓ.Prime) (hlarge : SptCM.cutoff ≤ ℓ) :
    ¬ CanonicalCongruencePrime ℓ := by
  letI : Fact ℓ.Prime := ⟨hprime⟩
  obtain ⟨n, hsquarefree, hmod, hinert, hsmall, hdegreePos, hdegreeLt⟩ :=
    small_n_of_E10 hE10 ℓ hlarge
  intro hcanonical
  exact (hnonzero ℓ n hsquarefree hmod hinert hsmall hdegreePos hdegreeLt)
    (hzero ℓ n hcanonical hsquarefree hmod hinert)

/-- Once the paper-internal argument excludes every canonical prime at or
above the cutoff, Andrews' exact congruences and Ahlgren--Kim's exact finite
exclusion yield the classification. -/
theorem classification_of_E1_E2_and_large_exclusion
    (hE1 : E1AndrewsCongruences)
    (hE2finite : E2AhlgrenKimFiniteExclusion)
    (hlarge : ∀ ℓ : ℕ, ℓ.Prime → 10 ^ 11 ≤ ℓ →
      ¬ CanonicalCongruencePrime ℓ) :
    RolenClassificationStatement := by
  have hsmall := canonical_small_primes_of_E1 hE1
  intro ℓ
  constructor
  · intro hcanonical
    by_cases hbelow : ℓ < 10 ^ 11
    · exact hE2finite ℓ hcanonical hbelow
    · exact (hlarge ℓ hcanonical.prime (Nat.le_of_not_gt hbelow)
        hcanonical).elim
  · rintro (rfl | rfl | rfl)
    · exact hsmall.1
    · exact hsmall.2.1
    · exact hsmall.2.2

end SptCM.Repair
