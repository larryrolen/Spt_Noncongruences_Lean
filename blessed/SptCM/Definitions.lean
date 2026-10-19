import Mathlib

/-!
# The smallest-parts function and canonical congruences

This file gives the elementary, combinatorial definitions used throughout the
formalization.  The value contributed by a partition is the multiplicity of
its least part; the empty partition contributes zero.
-/

namespace Nat

/-- The least nonnegative representative of the Bézout coefficient of `a`
modulo `n`.  When `a` and `n` are coprime and `n` is positive, this is the
multiplicative inverse of `a` modulo `n`.

This compatibility definition supplies the conventional `Nat.modInv` name,
which is not present in the Mathlib revision used by this project. -/
def modInv (a n : ℕ) : ℕ :=
  (gcdA a n % (n : ℤ)).toNat

end Nat

namespace SptCM

/-- The multiplicity of the least part of a partition.  The unique partition
of zero has no parts and is assigned weight zero. -/
def smallestPartMultiplicity {n : ℕ} (p : Nat.Partition n) : ℕ :=
  if h : p.parts.toFinset.Nonempty then
    p.parts.count (p.parts.toFinset.min' h)
  else
    0

/-- Andrews' smallest-parts function: the total number of occurrences of the
smallest part among all partitions of `n`. -/
def spt (n : ℕ) : ℕ :=
  ∑ p : Nat.Partition n, smallestPartMultiplicity p

/-- The canonical residue `b_ℓ`, represented by the inverse of 24 modulo `ℓ`.
For primes `ℓ ≥ 5`, this lies in `{1, ..., ℓ - 1}`. -/
def canonicalResidue (ℓ : ℕ) : ℕ :=
  Nat.modInv 24 ℓ

/-- A canonical congruence prime for `spt`: a prime `ℓ ≥ 5` for which the
canonical progression is identically zero modulo `ℓ`. -/
def CanonicalCongruencePrime (ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ 5 ≤ ℓ ∧ ∀ n : ℕ, ℓ ∣ spt (ℓ * n + canonicalResidue ℓ)

@[simp] theorem smallestPartMultiplicity_eq_of_parts_toFinset_nonempty
    {n : ℕ} (p : Nat.Partition n) (h : p.parts.toFinset.Nonempty) :
    smallestPartMultiplicity p = p.parts.count (p.parts.toFinset.min' h) := by
  simp [smallestPartMultiplicity, h]

@[simp] theorem smallestPartMultiplicity_eq_zero_of_parts_toFinset_not_nonempty
    {n : ℕ} (p : Nat.Partition n) (h : ¬ p.parts.toFinset.Nonempty) :
    smallestPartMultiplicity p = 0 := by
  simp [smallestPartMultiplicity, h]

@[simp] theorem canonicalResidue_eq_modInv (ℓ : ℕ) :
    canonicalResidue ℓ = Nat.modInv 24 ℓ := rfl

/-- A canonical congruence prime is prime. -/
theorem CanonicalCongruencePrime.prime {ℓ : ℕ}
    (h : CanonicalCongruencePrime ℓ) : ℓ.Prime :=
  h.1

/-- Canonical congruence primes are in the range considered in the paper. -/
theorem CanonicalCongruencePrime.five_le {ℓ : ℕ}
    (h : CanonicalCongruencePrime ℓ) : 5 ≤ ℓ :=
  h.2.1

/-- The divisibility assertion furnished by a canonical congruence prime. -/
theorem CanonicalCongruencePrime.dvd_spt {ℓ : ℕ}
    (h : CanonicalCongruencePrime ℓ) (n : ℕ) :
    ℓ ∣ spt (ℓ * n + canonicalResidue ℓ) :=
  h.2.2 n

end SptCM
