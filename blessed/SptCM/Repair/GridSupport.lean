import blessed.SptCM.Analytic.ThetaHecke

/-!
# Range-correct grid theta propagation

The Hecke recursion is used only at indices coprime to `6ℓ`.  In particular,
the characteristic prime itself can never be an induction factor.
-/

namespace SptCM.Repair

/-- The exact range of grid indices in Rolen's support proposition. -/
def GridIndexAllowed (ℓ m : ℕ) : Prop := Nat.Coprime m (6 * ℓ)

@[simp] theorem gridIndexAllowed_one (ℓ : ℕ) : GridIndexAllowed ℓ 1 := by
  simp [GridIndexAllowed]

/-- Allowed grid indices are closed under multiplication. -/
theorem gridIndexAllowed_mul {ℓ m p : ℕ}
    (hm : GridIndexAllowed ℓ m) (hp : GridIndexAllowed ℓ p) :
    GridIndexAllowed ℓ (m * p) := by
  exact Nat.coprime_mul_iff_left.mpr ⟨hm, hp⟩

/-- The characteristic prime is forbidden as a grid index.  This is the
regression statement excluding the invalid `m = ℓ` base step. -/
theorem not_gridIndexAllowed_self {ℓ : ℕ} (hprime : ℓ.Prime) :
    ¬ GridIndexAllowed ℓ ℓ := by
  intro h
  have hone : ℓ = 1 := h.eq_one_of_dvd (by simp)
  exact hprime.ne_one hone

/-- Range-correct input for grid theta propagation.  The induction step asks
for both the current index and the new prime factor to be coprime to `6ℓ`.
Thus it cannot be instantiated at `p = ℓ`, `p = 2`, or `p = 3`. -/
structure RestrictedGridThetaData
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (ℓ : ℕ) (theta : V →ₗ[K] V) (epsilon : K) (G : ℕ → V) : Prop where
  base : SptCM.Analytic.IsThetaEigen theta epsilon (G 1)
  step : ∀ m p : ℕ,
    GridIndexAllowed ℓ m → p.Prime → GridIndexAllowed ℓ p →
    SptCM.Analytic.IsThetaEigen theta epsilon (G m) →
    SptCM.Analytic.IsThetaEigen theta epsilon (G (m * p))

/-- A product of allowed indices is allowed. -/
theorem gridIndexAllowed_listProd {ℓ : ℕ} {factors : List ℕ}
    (hallowed : ∀ p ∈ factors, GridIndexAllowed ℓ p) :
    GridIndexAllowed ℓ factors.prod := by
  induction factors with
  | nil => simp
  | cons p ps ih =>
      rw [List.prod_cons]
      exact gridIndexAllowed_mul (hallowed p (by simp))
        (ih (fun q hq => hallowed q (by simp [hq])))

/-- Prime-factor induction for grid theta support, with all range conditions
threaded through the recursion. -/
theorem gridTheta_support_of_allowed_factorization
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ℓ : ℕ} {theta : V →ₗ[K] V} {epsilon : K} {G : ℕ → V}
    (d : RestrictedGridThetaData K V ℓ theta epsilon G)
    (factors : List ℕ)
    (hprime : ∀ p ∈ factors, p.Prime)
    (hallowed : ∀ p ∈ factors, GridIndexAllowed ℓ p) :
    SptCM.Analytic.IsThetaEigen theta epsilon (G factors.prod) := by
  induction factors with
  | nil => simpa using d.base
  | cons p ps ih =>
      have htailPrime : ∀ q ∈ ps, q.Prime :=
        fun q hq => hprime q (by simp [hq])
      have htailAllowed : ∀ q ∈ ps, GridIndexAllowed ℓ q :=
        fun q hq => hallowed q (by simp [hq])
      have htail := ih htailPrime htailAllowed
      have hstep := d.step ps.prod p
        (gridIndexAllowed_listProd htailAllowed)
        (hprime p (by simp)) (hallowed p (by simp)) htail
      simpa [List.prod_cons, Nat.mul_comm] using hstep

end SptCM.Repair
