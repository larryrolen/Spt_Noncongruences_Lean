module

public import blessed.SptCM.Interfaces
public import blessed.SptCM.Lemmas.Polynomial

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace SptCM

open Polynomial

/-- Under the paper's four deep external interfaces, no prime at or above the
Ahlgren--Kim cutoff is a canonical congruence prime. -/
theorem no_canonical_above_cutoff
    (h : ℕ → ℕ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hsmall : SmallDiscriminantInput h)
    (hdeg : ClassPolyDegreeInput h A B)
    (hobs : ObstructionInput A B)
    (hsep : SeparationInput A B) :
    ∀ ℓ, ℓ.Prime → cutoff ≤ ℓ → ¬ CanonicalCongruencePrime ℓ := by
  intro ℓ hprime hlarge hcanonical
  obtain ⟨n, hadmissible, hcollision, hdegree_pos, hdegree_lt⟩ :=
    hsmall ℓ hprime hlarge
  have hdata := hdeg ℓ n
  have hmonic : (A ℓ n).Monic := hdata.1
  have hnatDegree : (A ℓ n).natDegree = 2 * h n := hdata.2.2.1
  have hcop : IsCoprime (A ℓ n) (B ℓ n) :=
    hsep ℓ n hprime hadmissible hcollision
  have hnonzero : wronskianObstruction (A ℓ n) (B ℓ n) ≠ 0 :=
    wronskianObstruction_ne_zero_zmod hprime hcop hmonic
      (hnatDegree ▸ hdegree_pos) (hnatDegree ▸ hdegree_lt)
  exact hnonzero (hobs ℓ n hcanonical hadmissible)

/-- Conditional formalization of the paper's main theorem.  Every argument
listed here is an explicit external theorem interface; the proof itself uses no
axioms and formalizes the class-polynomial contradiction and cutoff split. -/
theorem canonicalCongruencePrime_iff
    (h : ℕ → ℕ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (h5 : Andrews5) (h7 : Andrews7) (h13 : Andrews13)
    (hfinite : FiniteExclusion)
    (hsmall : SmallDiscriminantInput h)
    (hdeg : ClassPolyDegreeInput h A B)
    (hobs : ObstructionInput A B)
    (hsep : SeparationInput A B) :
    ∀ ℓ, CanonicalCongruencePrime ℓ ↔ ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 := by
  intro ℓ
  constructor
  · intro hcanonical
    have hprime := hcanonical.prime
    by_cases hbelow : ℓ < cutoff
    · exact hfinite ℓ hcanonical hbelow
    · exact (no_canonical_above_cutoff h A B hsmall hdeg hobs hsep ℓ hprime
        (Nat.le_of_not_gt hbelow) hcanonical).elim
  · rintro (rfl | rfl | rfl)
    · exact h5
    · exact h7
    · exact h13

end SptCM
