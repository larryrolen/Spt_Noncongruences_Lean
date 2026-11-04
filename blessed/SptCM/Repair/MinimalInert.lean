module

public import blessed.SptCM.Repair.TrevinoBridge

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# The minimal inert progression discriminant

This file records the two elementary deductions made from the first exceptional
progression index in the final small-discriminant argument.  The analytic input
is precisely the corrected Treviño estimate E10.
-/

namespace SptCM.Repair

open SptCM.RolenLiterature

/-- The discriminant attached to the first exceptional progression index is
inert, rather than divisible by the modulus. -/
theorem minimalExceptionalIndex_inert
    (hE10 : E10TrevinoCorrected)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    legendreSym ℓ
      (-(24 * SptCM.firstNonresidue ℓ - 1 : ℕ) : ℤ) = -1 := by
  let k := SptCM.firstNonresidue ℓ
  let n := 24 * k - 1
  have hex := SptCM.firstNonresidue_exists hlarge
  have hkspec := SptCM.firstNonresidue_spec hex
  have hkbound := firstNonresidue_bound_of_E10 hE10 hlarge
  have hnsq : (n + 1) ^ 2 < 24 * ℓ := by
    have hksq := SptCM.progression_index_square_lt hlarge hkbound
    have hnadd : n + 1 = 24 * k := by
      dsimp [n]
      omega
    rw [hnadd]
    exact hksq
  have hnpos : 0 < n := by
    have hkpos : 0 < k := hkspec.1
    dsimp [n]
    omega
  have hnlt : n < ℓ :=
    SptCM.n_lt_modulus_of_succ_sq_lt
      (by
        have : 24 < SptCM.cutoff := by norm_num [SptCM.cutoff]
        omega)
      hnsq
  have hncast : (n : ZMod ℓ) ≠ 0 := by
    intro hz
    have hdvd : ℓ ∣ n := (ZMod.natCast_eq_zero_iff n ℓ).mp hz
    have := Nat.le_of_dvd hnpos hdvd
    omega
  have hnum : (1 : ℤ) - 24 * (k : ℤ) = -(n : ℤ) := by
    dsimp [n]
    omega
  have hneone : legendreSym ℓ (-(n : ℤ)) ≠ 1 := by
    rw [← hnum]
    exact hkspec.2
  have hnonzero : ((-(n : ℤ) : ℤ) : ZMod ℓ) ≠ 0 := by
    push_cast
    exact neg_ne_zero.mpr hncast
  have hneg : legendreSym ℓ (-(n : ℤ)) = -1 :=
    (legendreSym.eq_neg_one_iff_not_one ℓ hnonzero).2 hneone
  simpa [n, k] using hneg

/-- The discriminant attached to the first exceptional progression index is
squarefree.  Removing a prime-square factor would give a smaller member of the
same inert progression, contradicting minimality. -/
theorem minimalExceptionalIndex_squarefree
    (hE10 : E10TrevinoCorrected)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    Squarefree (24 * SptCM.firstNonresidue ℓ - 1) := by
  let k := SptCM.firstNonresidue ℓ
  let n := 24 * k - 1
  have hex := SptCM.firstNonresidue_exists hlarge
  have hkspec := SptCM.firstNonresidue_spec hex
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hnmod : n % 24 = 23 := by
    dsimp [n]
    omega
  have hinert : ¬ IsSquare (-(n : ZMod ℓ)) := by
    have hneg := minimalExceptionalIndex_inert hE10 hlarge
    have hneg' : legendreSym ℓ (-(n : ℤ)) = -1 := by
      simpa [n, k] using hneg
    simpa only [Int.cast_neg, Int.cast_natCast] using
      (legendreSym.eq_neg_one_iff ℓ).1 hneg'
  have hminimal : ∀ m : ℕ, 0 < m → m < n →
      ¬ (m % 24 = 23 ∧ ¬ IsSquare (-(m : ZMod ℓ))) := by
    intro m hmpos hmlt hmprop
    rcases hmprop with ⟨hmmod, hminert⟩
    let j := (m + 1) / 24
    have hmadd : m + 1 = 24 * j := by
      dsimp [j]
      omega
    have hjpos : 0 < j := by omega
    have hjlt : j < k := by
      dsimp [n] at hmlt
      omega
    have hmchar : legendreSym ℓ (-(m : ℤ)) = -1 := by
      rw [legendreSym.eq_neg_one_iff]
      simpa using hminert
    have hinterval := SptCM.character_interval_progression hex hjpos hjlt
    have harg : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ) := by
      exact_mod_cast
        (by omega : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ))
    rw [harg, hmchar] at hinterval
    omega
  have hsquarefree : Squarefree n := by
    apply SptCM.squarefree_of_minimal_congruence_character
      (fun m => m % 24 = 23)
      (fun m => ¬ IsSquare (-(m : ZMod ℓ)))
      hnpos hnmod hinert hminimal
    · intro p q hp hfactor
      exact (SptCM.primeSquare_invariance hp hfactor hnmod hinert).1
    · intro p q hp hfactor
      exact (SptCM.primeSquare_invariance hp hfactor hnmod hinert).2
  simpa [n, k] using hsquarefree

end SptCM.Repair
