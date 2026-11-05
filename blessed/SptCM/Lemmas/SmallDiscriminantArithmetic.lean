module

public import blessed.SptCM.Interfaces

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Elementary arithmetic for the small-discriminant lemma

This file isolates the part of Lemma 7.1 which follows after the analytic
character bound.  Square-root inequalities are recorded in their equivalent
integer-cleared form, so no real-analysis interface is needed.
-/

namespace SptCM

/-- The integer inequality `n² < 24ℓ`, expressing `n < √(24ℓ)`,
forces `n < ℓ` as soon as `ℓ ≥ 24`. -/
theorem n_lt_modulus_of_sq_lt
    {n ℓ : ℕ} (hℓ : 24 ≤ ℓ) (hsq : n ^ 2 < 24 * ℓ) :
    n < ℓ := by
  nlinarith

/-- The cleared inequality `(n+1)² < 24ℓ` forces `n < ℓ` as soon as
`ℓ ≥ 24`.  This is the integer form of the paper's deduction from
`n + 1 < √(24ℓ)`. -/
theorem n_lt_modulus_of_succ_sq_lt
    {n ℓ : ℕ} (hℓ : 24 ≤ ℓ) (hsq : (n + 1) ^ 2 < 24 * ℓ) :
    n < ℓ := by
  nlinarith

/-- Under the range `ℓ > 96` used in the paper, `n² < 24ℓ` implies
`2n < ℓ`.  This is the cleared version of
`2n < 2 √(24ℓ) < ℓ`. -/
theorem two_mul_lt_modulus_of_sq_lt
    {n ℓ : ℕ} (hℓ : 96 < ℓ) (hsq : n ^ 2 < 24 * ℓ) :
    2 * n < ℓ := by
  nlinarith

/-- The stronger bound on `n+1` also yields the preceding estimate. -/
theorem two_mul_lt_modulus_of_succ_sq_lt
    {n ℓ : ℕ} (hℓ : 96 < ℓ) (hsq : (n + 1) ^ 2 < 24 * ℓ) :
    2 * n < ℓ := by
  apply two_mul_lt_modulus_of_sq_lt hℓ
  simp only [pow_two] at hsq ⊢
  nlinarith

/-- If `h < n`, the cleared square-root bound `n² < 24ℓ` upgrades it
to `2h < ℓ` in the paper's range. -/
theorem two_classNumber_lt_modulus_of_sq_lt
    {h n ℓ : ℕ} (hℓ : 96 < ℓ) (hsq : n ^ 2 < 24 * ℓ)
    (hclass : h < n) :
    2 * h < ℓ := by
  have hn : 2 * n < ℓ := two_mul_lt_modulus_of_sq_lt hℓ hsq
  omega

/-- If an arithmetic class-number estimate gives `h < n`, the stronger
`(n+1)²` bound likewise gives the degree bound `2h < ℓ`. -/
theorem two_classNumber_lt_modulus
    {h n ℓ : ℕ} (hℓ : 96 < ℓ) (hsq : (n + 1) ^ 2 < 24 * ℓ)
    (hclass : h < n) :
    2 * h < ℓ := by
  have hn : 2 * n < ℓ := two_mul_lt_modulus_of_succ_sq_lt hℓ hsq
  omega

/-- A general minimality principle used by the squarefreeness argument.
If a property of `n` survives removal of every prime-square factor,
then a positive, minimal number with that property is squarefree. -/
theorem squarefree_of_minimal_square_invariant
    (P : ℕ → Prop) {n : ℕ}
    (hn : 0 < n) (hPn : P n)
    (hminimal : ∀ m : ℕ, 0 < m → m < n → ¬ P m)
    (hinvariant : ∀ p q : ℕ, p.Prime → n = p ^ 2 * q → P n → P q) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpdvd
  rcases hpdvd with ⟨q, hq⟩
  have hqpos : 0 < q := by
    by_contra hq0
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
    subst q
    simp at hq
    omega
  have hpp : 1 < p * p := by
    nlinarith [hp.two_le]
  have hqlt : q < n := by
    calc
      q < (p * p) * q := (Nat.lt_mul_iff_one_lt_left hqpos).2 hpp
      _ = n := hq.symm
  exact hminimal q hqpos hqlt
    (hinvariant p q hp (by simpa [pow_two] using hq) hPn)

/-- Paper-facing form of the preceding principle.  The two predicates stand
for the congruence condition (`m ≡ 23 mod 24`) and the inert character
condition.  Their invariance after dividing by a prime square is kept as an
explicit hypothesis, separating the elementary minimality argument from the
number-theoretic facts that establish those invariances. -/
theorem squarefree_of_minimal_congruence_character
    (CongruenceCondition CharacterCondition : ℕ → Prop) {n : ℕ}
    (hn : 0 < n)
    (hcongruence : CongruenceCondition n)
    (hcharacter : CharacterCondition n)
    (hminimal : ∀ m : ℕ, 0 < m → m < n →
      ¬(CongruenceCondition m ∧ CharacterCondition m))
    (hcongruence_invariant : ∀ p q : ℕ, p.Prime →
      n = p ^ 2 * q → CongruenceCondition q)
    (hcharacter_invariant : ∀ p q : ℕ, p.Prime →
      n = p ^ 2 * q → CharacterCondition q) :
    Squarefree n := by
  apply squarefree_of_minimal_square_invariant
    (fun m => CongruenceCondition m ∧ CharacterCondition m)
    hn ⟨hcongruence, hcharacter⟩ hminimal
  intro p q hp hfactor _
  exact ⟨hcongruence_invariant p q hp hfactor,
    hcharacter_invariant p q hp hfactor⟩

end SptCM
