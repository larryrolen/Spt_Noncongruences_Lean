module

public import blessed.SptCM.CM.Repaired.HauptmodulCoordinate
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SptCM.Analytic.Repaired

noncomputable section

/-- Cusp representatives in the order infinity, zero, one-half, one-third. -/
def i12CuspTransform (c : Fin 4) (z : ℂ) : ℂ :=
  if c = 0 then z else if c = 1 then -1 / z
  else if c = 2 then z / (2 * z + 1) else z / (3 * z + 1)

def i12CuspWidth (c : Fin 4) : ℕ :=
  if c = 0 then 1 else if c = 1 then 6 else if c = 2 then 3 else 2

/-- A genuine analytic realization of a rational-coefficient Laurent series.
The unitary transformation law is on Gamma_0(6), and every cusp has a
convergent local expansion with a nonvanishing analytic unit. Real orders
allow unitary multipliers; zero orders give ordinary holomorphic units.
The convergence requirement ties the analytic function to the formal series. -/
structure I12UnitaryMeromorphicRealization (f : LaurentSeries ℚ) where
  toFun : ℂ → ℂ
  meromorphic : MeromorphicOn toFun {z : ℂ | 0 < z.im}
  nonzeroOrder : ∀ z : ℂ, 0 < z.im → meromorphicOrderAt toFun z ≠ ⊤
  unitary : ∀ γ : SptCM.GammaZeroSixMatrix, ∃ u : ℂ, ‖u‖ = 1 ∧
    ∀ z : ℂ, 0 < z.im →
      toFun (((γ.p : ℂ) * z + γ.q) / ((γ.s : ℂ) * z + γ.t)) = u * toFun z
  expansion : ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im →
    HasSum (fun k : ℤ => (f.coeff k : ℂ) *
      (Complex.exp (2 * Real.pi * Complex.I * z)) ^ k) (toFun z)
  cuspOrder : Fin 4 → ℝ
  cuspExpansion : ∀ c : Fin 4, ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im →
      toFun (i12CuspTransform c z) =
        Complex.exp (2 * Real.pi * Complex.I * (cuspOrder c : ℂ) * z /
          (i12CuspWidth c : ℂ)) *
        U (Complex.exp (2 * Real.pi * Complex.I * z / (i12CuspWidth c : ℂ)))

def HasI12UnitaryMeromorphicRealization (f : LaurentSeries ℚ) : Prop :=
  Nonempty (I12UnitaryMeromorphicRealization f)

/-- The analytic domain is inhabited: the constant function one supplies
all transformation, convergence, nonvanishing and cusp conditions. -/
theorem one_hasI12UnitaryMeromorphicRealization :
    HasI12UnitaryMeromorphicRealization 1 := by
  classical
  refine ⟨{
    toFun := fun _ => 1
    meromorphic := ?_
    nonzeroOrder := ?_
    unitary := ?_
    expansion := ?_
    cuspOrder := fun _ => 0
    cuspExpansion := ?_ }⟩
  · exact fun _ _ => analyticAt_const.meromorphicAt
  · intro z hz
    simp [meromorphicOrderAt_const]
  · intro γ
    exact ⟨1, by simp, by intros; simp⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    convert (hasSum_ite_eq (0 : ℤ) (1 : ℂ)) using 1
    funext k
    by_cases hk : k = 0 <;> simp [HahnSeries.coeff_one, hk]
  · intro c
    refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, 1, by norm_num, ?_⟩
    intro z hz
    simp

end

end SptCM.Analytic.Repaired
