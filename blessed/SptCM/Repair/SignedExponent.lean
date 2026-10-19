import blessed.SptCM.Analytic.PaperCoefficientModels

/-!
# Signed Euler exponents

The exponent in Rolen's product is `χ₁₂(m) h_n(m²)`.  Its positive and
negative parts are natural exponents for numerator and denominator products.
-/

namespace SptCM.Repair

/-- The signed integer exponent occurring in the Borcherds product. -/
def signedEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℤ :=
  SptCM.Analytic.chi12 (m : ℤ) * H ((m : ℤ) ^ 2)

/-- Positive part of the signed Euler exponent. -/
def positiveEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℕ :=
  (signedEulerExponent H m).toNat

/-- Negative part of the signed Euler exponent. -/
def negativeEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℕ :=
  (-signedEulerExponent H m).toNat

/-- The complete, pointwise specification of the positive/negative
decomposition used to construct the two Euler products. -/
def SignedExponentSpec (H : ℤ → ℤ) (m : ℕ) : Prop :=
  ((positiveEulerExponent H m : ℤ) -
      (negativeEulerExponent H m : ℤ) = signedEulerExponent H m) ∧
    (positiveEulerExponent H m = 0 ∨
      negativeEulerExponent H m = 0) ∧
    (¬ Nat.Coprime m 6 → signedEulerExponent H m = 0)

/-- The positive-minus-negative decomposition recovers the exact signed
integer exponent. -/
theorem positive_sub_negativeEulerExponent (H : ℤ → ℤ) (m : ℕ) :
    (positiveEulerExponent H m : ℤ) -
      (negativeEulerExponent H m : ℤ) = signedEulerExponent H m := by
  exact Int.toNat_sub_toNat_neg (signedEulerExponent H m)

/-- At most one of the positive and negative exponents is nonzero. -/
theorem positive_or_negativeEulerExponent_eq_zero
    (H : ℤ → ℤ) (m : ℕ) :
    positiveEulerExponent H m = 0 ∨ negativeEulerExponent H m = 0 := by
  by_cases h : 0 ≤ signedEulerExponent H m
  · right
    simp [negativeEulerExponent, Int.toNat_eq_zero, h]
  · left
    simp [positiveEulerExponent, Int.toNat_eq_zero, le_of_not_ge h]

/-- Reduction modulo a prime preserves the signed exponent identity. -/
theorem positive_sub_negativeEulerExponent_zmod
    (ℓ : ℕ) (H : ℤ → ℤ) (m : ℕ) :
    (positiveEulerExponent H m : ZMod ℓ) -
      (negativeEulerExponent H m : ZMod ℓ) =
        (signedEulerExponent H m : ZMod ℓ) := by
  have h := congrArg (fun z : ℤ => (z : ZMod ℓ))
    (positive_sub_negativeEulerExponent H m)
  push_cast at h
  exact h

/-- Failure of coprimality with six is exactly enough to force divisibility by
one of its prime factors. -/
theorem two_dvd_or_three_dvd_of_not_coprime_six
    {m : ℕ} (h : ¬ Nat.Coprime m 6) : 2 ∣ m ∨ 3 ∣ m := by
  by_contra hdiv
  push Not at hdiv
  have hc2 : Nat.Coprime m 2 :=
    Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).2 hdiv.1)
  have hc3 : Nat.Coprime m 3 :=
    Nat.coprime_comm.mp ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd.2 hdiv.2)
  apply h
  simpa using hc2.mul_right hc3

/-- `χ₁₂` vanishes away from indices coprime to six. -/
theorem chi12_eq_zero_of_not_coprime_six
    {m : ℕ} (h : ¬ Nat.Coprime m 6) :
    SptCM.Analytic.chi12 (m : ℤ) = 0 := by
  rcases two_dvd_or_three_dvd_of_not_coprime_six h with htwo | hthree
  · rcases htwo with ⟨k, rfl⟩
    simp only [SptCM.Analytic.chi12]
    split_ifs <;> omega
  · rcases hthree with ⟨k, rfl⟩
    simp only [SptCM.Analytic.chi12]
    split_ifs <;> omega

/-- Consequently all numerator and denominator exponents vanish at indices
not coprime to six. -/
theorem signedEulerExponent_eq_zero_of_not_coprime_six
    (H : ℤ → ℤ) {m : ℕ} (h : ¬ Nat.Coprime m 6) :
    signedEulerExponent H m = 0 := by
  simp [signedEulerExponent, chi12_eq_zero_of_not_coprime_six h]

/-- The signed exponent and its natural positive and negative parts satisfy
the full specification, including the zero-character case. -/
theorem signedExponentSpec (H : ℤ → ℤ) (m : ℕ) :
    SignedExponentSpec H m := by
  exact ⟨positive_sub_negativeEulerExponent H m,
    positive_or_negativeEulerExponent_eq_zero H m,
    signedEulerExponent_eq_zero_of_not_coprime_six H⟩

/-- The two verified square-coefficient endpoints (`m=1` and `m>1`
coprime to six) suffice for every Euler index: the remaining indices have
zero character.  This is the exact bridge needed before Frobenius is applied
to the canonical products. -/
theorem signedEulerExponent_cast_eq_zero_of_square_endpoints
    (ℓ : ℕ) (H : ℤ → ℤ)
    (hfirst : (H 1 : ZMod ℓ) = 0)
    (hsquare : ∀ m : ℕ, 1 < m → Nat.Coprime m 6 →
      (H ((m : ℤ) ^ 2) : ZMod ℓ) = 0)
    (m : ℕ) :
    (signedEulerExponent H m : ZMod ℓ) = 0 := by
  by_cases hm6 : Nat.Coprime m 6
  · rcases m with _ | m
    · norm_num at hm6
    · rcases m with _ | m
      · simp [signedEulerExponent, hfirst]
      · have hz : (H (((m + 2 : ℕ) : ℤ) ^ 2) : ZMod ℓ) = 0 :=
          hsquare (m + 2) (by omega) (by simpa [Nat.add_assoc] using hm6)
        rw [signedEulerExponent]
        push_cast
        rw [show ((m : ℤ) + 1 + 1) = ((m + 2 : ℕ) : ℤ) by push_cast; omega,
          hz, mul_zero]
  · rw [show signedEulerExponent H m = 0 from
      signedEulerExponent_eq_zero_of_not_coprime_six H hm6]
    exact Int.cast_zero

end SptCM.Repair
