import blessed.SptCM.Repair.AnalyticFormalIdentification
namespace SptCM.Repair
open scoped PowerSeries
variable {R : Type*} [CommRing R]
def LowOne (P : PowerSeries R) (m : ℕ) : Prop :=
  ∀ n < m, PowerSeries.coeff n P = PowerSeries.coeff n 1
lemma coeff_mul_low (P Q : PowerSeries R) (n : ℕ)
    (hQ : ∀ j ≤ n, PowerSeries.coeff j Q = PowerSeries.coeff j 1) :
    PowerSeries.coeff n (P*Q) = PowerSeries.coeff n P := by
  rw [PowerSeries.coeff_mul]
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff ij.1 P * PowerSeries.coeff ij.2 1 := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hQ ij.2 (by
        have hs : ij.1 + ij.2 = n := by simpa using hij
        omega)]
    _ = PowerSeries.coeff n (P * 1) := by rw [PowerSeries.coeff_mul]
    _ = PowerSeries.coeff n P := by simp
lemma LowOne.mul {P Q : PowerSeries R} {m : ℕ} (hP : LowOne P m) (hQ : LowOne Q m) :
    LowOne (P*Q) m := by
  intro n hn
  rw [coeff_mul_low P Q n (fun j hj => hQ j (lt_of_le_of_lt hj hn))]
  exact hP n hn
lemma LowOne.pow {P : PowerSeries R} {m : ℕ} (hP : LowOne P m) (a : ℕ) :
    LowOne (P^a) m := by
  induction a with
  | zero => simp [LowOne]
  | succ a ih => rw [pow_succ]; exact ih.mul hP
lemma low_sub_X_pow (k m : ℕ) (hmk : m ≤ k) :
    LowOne (1 - (PowerSeries.X : PowerSeries R)^k) m := by
  intro n hn
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  have hne : n ≠ k := by omega
  simp [hne]
lemma low_subst_inv (k a m : ℕ) (hk : k ≠ 0) (hmk : m ≤ k) :
    LowOne (PowerSeries.subst ((PowerSeries.X : PowerSeries R)^k)
      (PowerSeries.invOneSubPow R a : PowerSeries R)) m := by
  intro n hn
  rw [PowerSeries.coeff_subst_X_pow (R:=R) (S:=R) hk]
  by_cases hn0 : n=0
  · subst n
    cases a <;> simp [PowerSeries.invOneSubPow]
  · have hnd : ¬ k ∣ n := by
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < n) hd
      omega
    simp [hnd, hn0]
end SptCM.Repair
