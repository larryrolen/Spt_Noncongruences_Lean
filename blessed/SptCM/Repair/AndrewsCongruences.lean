import blessed.SptCM.Literature.RolenLiterature

/-!
# Exact application of Andrews' three SPT congruences

The external statements use Andrews' published shifts `4`, `5`, and `6`.
This file computes the project's canonical residue from its Bézout definition
and proves internally that those three statements give the positive direction
of Rolen's classification.
-/

namespace SptCM.Repair

open SptCM.RolenLiterature

@[simp] theorem canonicalResidue_five : canonicalResidue 5 = 4 := by
  unfold canonicalResidue Nat.modInv Nat.gcdA Nat.xgcd
  simp only [Nat.xgcdAux, Nat.strongRec_eq]
  norm_num
  exact_mod_cast Int.toNat_of_nonneg (show (0 : ℤ) ≤ 4 by norm_num)

@[simp] theorem canonicalResidue_seven : canonicalResidue 7 = 5 := by
  unfold canonicalResidue Nat.modInv Nat.gcdA Nat.xgcd
  simp only [Nat.xgcdAux, Nat.strongRec_eq]
  norm_num
  exact_mod_cast Int.toNat_of_nonneg (show (0 : ℤ) ≤ 5 by norm_num)

@[simp] theorem canonicalResidue_thirteen : canonicalResidue 13 = 6 := by
  unfold canonicalResidue Nat.modInv Nat.gcdA Nat.xgcd
  simp only [Nat.xgcdAux, Nat.strongRec_eq]
  norm_num
  exact_mod_cast Int.toNat_of_nonneg (show (0 : ℤ) ≤ 6 by norm_num)

/-- Andrews' published modulus-five congruence implies that `5` is canonical. -/
theorem canonical_five_of_Andrews (h : SptProgressionCongruence 5 4) :
    CanonicalCongruencePrime 5 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k
  rw [canonicalResidue_five]
  exact h k

/-- Andrews' published modulus-seven congruence implies that `7` is canonical. -/
theorem canonical_seven_of_Andrews (h : SptProgressionCongruence 7 5) :
    CanonicalCongruencePrime 7 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k
  rw [canonicalResidue_seven]
  exact h k

/-- Andrews' published modulus-thirteen congruence implies that `13` is
canonical. -/
theorem canonical_thirteen_of_Andrews (h : SptProgressionCongruence 13 6) :
    CanonicalCongruencePrime 13 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k
  rw [canonicalResidue_thirteen]
  exact h k

/-- The exact E1 ledger entry supplies the three positive cases, while all
range and residue normalization facts are checked internally. -/
theorem canonical_small_primes_of_E1 (hE1 : E1AndrewsCongruences) :
    CanonicalCongruencePrime 5 ∧ CanonicalCongruencePrime 7 ∧
      CanonicalCongruencePrime 13 :=
  ⟨canonical_five_of_Andrews hE1.1,
    canonical_seven_of_Andrews hE1.2.1,
    canonical_thirteen_of_Andrews hE1.2.2⟩

end SptCM.Repair
