module

public import blessed.SptCM.Definitions
public import blessed.SptCM.Lemmas.Polynomial
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Field.ZMod

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace SptCM

open Polynomial

/-- An auxiliary squarefree index in the progression `23 mod 24` at which
`-n` is a quadratic nonresidue modulo `ℓ`. -/
@[expose]
def Admissible (ℓ n : ℕ) : Prop :=
  Squarefree n ∧ n % 24 = 23 ∧ ¬ IsSquare (-(n : ZMod ℓ))

/-- The cutoff up to which Ahlgren--Kim's finite computation applies. -/
@[expose]
def cutoff : ℕ := 10 ^ 11

/-- The external Andrews congruence at 5, packaged as a proposition. -/
@[expose]
def Andrews5 : Prop := CanonicalCongruencePrime 5

/-- The external Andrews congruence at 7, packaged as a proposition. -/
@[expose]
def Andrews7 : Prop := CanonicalCongruencePrime 7

/-- The external Andrews congruence at 13, packaged as a proposition. -/
@[expose]
def Andrews13 : Prop := CanonicalCongruencePrime 13

/-- The exact finite-range consequence imported from Ahlgren--Kim. -/
@[expose]
def FiniteExclusion : Prop :=
  ∀ ℓ, CanonicalCongruencePrime ℓ → ℓ < cutoff →
    ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13

/-- The small inert discriminant consequence of Treviño's character estimate
and the elementary class-number bound. -/
@[expose]
def SmallDiscriminantSpec (h : ℕ → ℕ) (ℓ n : ℕ) : Prop :=
  Admissible ℓ n ∧ (n + 1) ^ 2 < 24 * ℓ ∧
    0 < 2 * h n ∧ 2 * h n < ℓ

/-- The small inert discriminant consequence of Treviño's character estimate
and the elementary class-number bound. -/
@[expose]
def SmallDiscriminantInput (h : ℕ → ℕ) : Prop :=
  ∀ ℓ, ℓ.Prime → cutoff ≤ ℓ → ∃ n,
    SmallDiscriminantSpec h ℓ n

/-- The monicity and degree consequence of the oriented CM class-polynomial
construction. -/
@[expose]
def ClassPolyDegreeInput (h : ℕ → ℕ)
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, (A ℓ n).Monic ∧ (B ℓ n).Monic ∧
    (A ℓ n).natDegree = 2 * h n ∧ (B ℓ n).natDegree = 2 * h n

/-- The modular-form and Borcherds-product consequence: a canonical
congruence forces the class-polynomial obstruction to vanish. -/
@[expose]
def ObstructionInput
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, CanonicalCongruencePrime ℓ → Admissible ℓ n →
    wronskianObstruction (A ℓ n) (B ℓ n) = 0

/-- The CM specialization and Eichler-order volume consequence: below the
collision bound, the two oriented class polynomials remain coprime. -/
@[expose]
def SeparationInput
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, ℓ.Prime → Admissible ℓ n → (n + 1) ^ 2 < 24 * ℓ →
    IsCoprime (A ℓ n) (B ℓ n)

end SptCM
