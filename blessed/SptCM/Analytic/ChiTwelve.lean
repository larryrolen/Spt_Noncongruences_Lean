import Mathlib

/-!
# The quadratic character modulo twelve
-/

namespace SptCM.Analytic

/-- The quadratic character `χ₁₂(m) = (12/m)`, explicitly by residue class. -/
def chi12 (m : ℤ) : ℤ :=
  if m % 12 = 1 ∨ m % 12 = 11 then 1
  else if m % 12 = 5 ∨ m % 12 = 7 then -1
  else 0

/-- The same character on the canonical finite residue type. -/
def chi12Residue (r : Fin 12) : ℤ :=
  if r.val = 1 ∨ r.val = 11 then 1
  else if r.val = 5 ∨ r.val = 7 then -1
  else 0

/-- The residue table is multiplicative. -/
theorem chi12Residue_mul (a b : Fin 12) :
    chi12Residue (a * b) = chi12Residue a * chi12Residue b := by
  fin_cases a <;> fin_cases b <;> decide

/-- On residue classes prime to six, the quadratic character has square one. -/
theorem chi12Residue_sq_of_coprime_six (r : Fin 12)
    (hr : Nat.Coprime r.val 6) :
    chi12Residue r ^ 2 = 1 := by
  fin_cases r <;> simp_all [chi12Residue, Nat.Coprime]

/-- Canonical residue of a natural number modulo twelve. -/
def natResidueTwelve (m : ℕ) : Fin 12 := ⟨m % 12, Nat.mod_lt _ (by norm_num)⟩

theorem natResidueTwelve_mul (a b : ℕ) :
    natResidueTwelve (a * b) = natResidueTwelve a * natResidueTwelve b := by
  apply Fin.ext
  change (a * b) % 12 = (a % 12 * (b % 12)) % 12
  exact Nat.mul_mod a b 12

/-- The integer-indexed definition agrees with the finite residue table on
natural indices. -/
theorem chi12_nat_eq_residue (m : ℕ) :
    chi12 (m : ℤ) = chi12Residue (natResidueTwelve m) := by
  simp only [chi12, chi12Residue, natResidueTwelve]
  norm_cast

/-- Multiplicativity of the actual character on natural indices. -/
theorem chi12_nat_mul (a b : ℕ) :
    chi12 ((a * b : ℕ) : ℤ) = chi12 (a : ℤ) * chi12 (b : ℤ) := by
  rw [chi12_nat_eq_residue, chi12_nat_eq_residue, chi12_nat_eq_residue,
    natResidueTwelve_mul, chi12Residue_mul]

/-- The actual character has square one at every natural index coprime to
six. -/
theorem chi12_nat_sq_of_coprime_six (m : ℕ) (hm : Nat.Coprime m 6) :
    chi12 (m : ℤ) ^ 2 = 1 := by
  rw [chi12_nat_eq_residue]
  apply chi12Residue_sq_of_coprime_six
  apply (ZMod.coprime_mod_iff_coprime (m % 12) 6).mp
  have hm6 : Nat.Coprime (m % 6) 6 :=
    (ZMod.coprime_mod_iff_coprime m 6).mpr hm
  simpa [Nat.mod_mod_of_dvd m (by norm_num : 6 ∣ 12)] using hm6

/-- Multiplicativity remains true after casting the integer-valued character
to any ring. -/
theorem chi12_nat_mul_cast {K : Type*} [Ring K] (a b : ℕ) :
    (chi12 ((a * b : ℕ) : ℤ) : K) =
      (chi12 (a : ℤ) : K) * (chi12 (b : ℤ) : K) := by
  simpa only [Int.cast_mul] using
    congrArg (fun z : ℤ => (z : K)) (chi12_nat_mul a b)

/-- The square-one identity remains true after casting to any ring. -/
theorem chi12_nat_sq_cast_of_coprime_six
    {K : Type*} [Ring K] (m : ℕ) (hm : Nat.Coprime m 6) :
    (chi12 (m : ℤ) : K) ^ 2 = 1 := by
  simpa only [Int.cast_pow, Int.cast_one] using
    congrArg (fun z : ℤ => (z : K)) (chi12_nat_sq_of_coprime_six m hm)

end SptCM.Analytic
