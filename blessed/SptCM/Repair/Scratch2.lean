import blessed.SptCM.Repair.AnalyticFormalIdentification
namespace SptCM.Repair
noncomputable def af (q : ℂ) (m : ℕ) : ℂ :=
  (1-q^m)^5 * (1-q^(3*m)) * (1/(1-q^(2*m))) * (1/(1-q^(6*m))^5)
example (q : ℂ) (N : ℕ) :
    hauptmodulEulerPartial q N = ∏ i ∈ Finset.range N, af q (i+1) := by
  simp only [hauptmodulEulerPartial, etaEulerPartial, af]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  simp only [← Finset.prod_pow, one_div]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring
end SptCM.Repair
#check Finset.prod_inv_distrib
#check Finset.prod_div_distrib
