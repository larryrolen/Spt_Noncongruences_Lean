import blessed.SptCM.Interfaces

/-!
# Arithmetic at the end of the quaternionic separation argument

The paper obtains `6 * p ≤ 4 * N(α) * N(β)` and, for the two CM
endomorphisms in question, both norms are `(n + 1) / 4`.  We avoid natural
number division by naming the common norm `m` and recording the exact cleared
identity `n + 1 = 4 * m`.
-/

namespace SptCM

open Polynomial

/-- The quaternionic volume estimate, after substituting the common norm and
clearing denominators, gives `24p ≤ (n+1)²`. -/
theorem cleared_square_bound_of_volume_bound
    {p n m : ℕ} (hnorm : n + 1 = 4 * m)
    (hvolume : 6 * p ≤ 4 * m ^ 2) :
    24 * p ≤ (n + 1) ^ 2 := by
  nlinarith [sq_nonneg (4 * m : ℤ)]

/-- Thus the volume estimate rules out the strict collision bound used in the
separation proposition. -/
theorem not_collision_bound_of_volume_bound
    {p n m : ℕ} (hnorm : n + 1 = 4 * m)
    (hvolume : 6 * p ≤ 4 * m ^ 2) :
    ¬((n + 1) ^ 2 < 24 * p) := by
  exact Nat.not_lt_of_ge (cleared_square_bound_of_volume_bound hnorm hvolume)

/-- The strict collision bound is exactly the negation of the integer-cleared
volume conclusion. -/
theorem collision_bound_iff_not_cleared_volume_bound {p n : ℕ} :
    (n + 1) ^ 2 < 24 * p ↔ ¬(24 * p ≤ (n + 1) ^ 2) := by
  exact lt_iff_not_ge

/-- A direct contradiction form, convenient at the end of the geometric
separation proof. -/
theorem volume_bound_and_collision_bound_false
    {p n m : ℕ} (hnorm : n + 1 = 4 * m)
    (hvolume : 6 * p ≤ 4 * m ^ 2)
    (hcollision : (n + 1) ^ 2 < 24 * p) : False := by
  exact not_collision_bound_of_volume_bound hnorm hvolume hcollision

/-- Paper-facing class-polynomial corollary: coprimality, monicity, and the
positive degree bound force the Wronskian obstruction to be nonzero. -/
theorem classPolynomial_obstruction_ne_zero
    (h : ℕ → ℕ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hdeg : ClassPolyDegreeInput h A B)
    {ℓ n : ℕ} (hprime : ℓ.Prime)
    (hcop : IsCoprime (A ℓ n) (B ℓ n))
    (hdegree_pos : 0 < 2 * h n) (hdegree_lt : 2 * h n < ℓ) :
    wronskianObstruction (A ℓ n) (B ℓ n) ≠ 0 := by
  have hdata := hdeg ℓ n
  have hmonic : (A ℓ n).Monic := hdata.1
  have hnatDegree : (A ℓ n).natDegree = 2 * h n := hdata.2.2.1
  exact wronskianObstruction_ne_zero_zmod hprime hcop hmonic
    (hnatDegree ▸ hdegree_pos) (hnatDegree ▸ hdegree_lt)

end SptCM
