import blessed.SptCM.Analytic.PaperCoefficientModels
import blessed.SptCM.Analytic.DualityPairing

/-!
# Concrete normalized coefficient objects used by the paper

These definitions give the exact Fourier normalizations independently of the
analytic modularity assertions.  Modularity and uniqueness are accepted only
as separate, precisely typed inputs to the corresponding theorems.
-/

namespace SptCM.Analytic

/-- A concrete coefficient series with the paper's grid principal part.
The positive coefficients remain parameters because their analytic
construction from `-Θj/η` and Faber polynomials is not present in Mathlib. -/
def canonicalGridSeries {R : Type*} [Ring R]
    (chi : ℕ → R) (m : ℕ) (positiveCoeff : ℤ → R) : QSeries R :=
  fun r =>
    if r = -(m : ℤ) ^ 2 then 1
    else if r = -1 then -chi m
    else if 0 < r then positiveCoeff r else 0

/-- The concrete grid series has exactly the prescribed negative principal
part, without any modularity assumption. -/
theorem canonicalGridSeries_hasGridPrincipalPart
    {R : Type*} [Ring R]
    (chi : ℕ → R) (m : ℕ) (positiveCoeff : ℤ → R) :
    HasGridPrincipalPart chi m (canonicalGridSeries chi m positiveCoeff) := by
  intro r hr
  by_cases hm : r = -(m : ℤ) ^ 2
  · simp [canonicalGridSeries, hm]
  · by_cases hone : r = -1
    · simp [canonicalGridSeries, hone]
    · have hpos : ¬ 0 < r := by omega
      simp [canonicalGridSeries, hm, hone, hpos]

/-- `G₁=0`, as in the paper's endpoint convention. -/
def paperGridForm {R : Type*} [Ring R]
    (chi : ℕ → R) (positiveCoeff : ℕ → ℤ → R) (m : ℕ) : QSeries R :=
  if m = 1 then 0 else canonicalGridSeries chi m (positiveCoeff m)

@[simp] theorem paperGridForm_one {R : Type*} [Ring R]
    (chi : ℕ → R) (positiveCoeff : ℕ → ℤ → R) :
    paperGridForm chi positiveCoeff 1 = 0 := by
  simp [paperGridForm]

/-- Away from the endpoint, the explicitly normalized grid form has the
paper's principal part. -/
theorem paperGridForm_principalPart
    {R : Type*} [Ring R]
    (chi : ℕ → R) (positiveCoeff : ℕ → ℤ → R)
    (m : ℕ) (hm : m ≠ 1) :
    HasGridPrincipalPart chi m (paperGridForm chi positiveCoeff m) := by
  rw [paperGridForm, if_neg hm]
  exact canonicalGridSeries_hasGridPrincipalPart chi m (positiveCoeff m)

/-- Exact paper-specific existence/uniqueness statement, derived from the
concrete normalization plus separate modularity and uniqueness facts. -/
theorem paperGridForm_existsUnique
    {R : Type*} [Ring R]
    (chi : ℕ → R) (positiveCoeff : ℕ → ℤ → R)
    (m : ℕ) (hm : 1 < m)
    (IsModular : QSeries R → Prop)
    (hmod : IsModular (paperGridForm chi positiveCoeff m))
    (hunique : ∀ g, IsModular g → HasGridPrincipalPart chi m g →
      g = paperGridForm chi positiveCoeff m) :
    ∃! g, IsModular g ∧ HasGridPrincipalPart chi m g := by
  refine ⟨paperGridForm chi positiveCoeff m,
    ⟨hmod, paperGridForm_principalPart chi positiveCoeff m (by omega)⟩, ?_⟩
  rintro g ⟨hgmod, hgpp⟩
  exact hunique g hgmod hgpp

/-- The exact `f` Hecke identity follows from grid uniqueness once the cited
shadow calculation and the explicit principal-part computation have shown
that both displayed sides qualify. -/
theorem paper_f_hecke_identity
    {K : Type*} [Field K]
    (ell : ℕ) (chiEll : K) (legendre : ℤ → K)
    (f Gell : QSeries K) (Qualifies : QSeries K → Prop)
    (hleft : Qualifies
      (fun r => heckeThreeHalf ell chiEll legendre f r -
        chiEll * (1 + (ell : K)) * f r))
    (hright : Qualifies (fun r => (ell : K) * Gell r))
    (hunique : ∀ x y, Qualifies x → Qualifies y → x = y) :
    (fun r => heckeThreeHalf ell chiEll legendre f r -
      chiEll * (1 + (ell : K)) * f r) =
      (fun r => (ell : K) * Gell r) :=
  hecke_identity_of_grid_uniqueness hleft hright hunique

/-- The exact grid Hecke recurrence follows from the same uniqueness step once
its two sides have separately been shown modular with the computed principal
part. -/
theorem paper_grid_hecke_identity
    {K : Type*} [Field K]
    (ell _m : ℕ) (chiEll chiM legendreM : K) (legendre : ℤ → K)
    (Gm Gmell GmDiv Gell : QSeries K) (Qualifies : QSeries K → Prop)
    (hleft : Qualifies (heckeThreeHalf ell chiEll legendre Gm))
    (hright : Qualifies (fun r =>
      (ell : K) * Gmell r + chiEll * legendreM * Gm r + GmDiv r -
        (ell : K) * chiM * Gell r))
    (hunique : ∀ x y, Qualifies x → Qualifies y → x = y) :
    heckeThreeHalf ell chiEll legendre Gm =
      (fun r => (ell : K) * Gmell r + chiEll * legendreM * Gm r + GmDiv r -
        (ell : K) * chiM * Gell r) :=
  hecke_identity_of_grid_uniqueness hleft hright hunique

/-- A dependency-first formulation of grid theta support: the prime base case
and the Hecke recurrence step imply the property along any supplied prime
factorization chain. -/
theorem grid_theta_support_along_chain
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (theta : V →ₗ[K] V) (epsilon : K) (G : ℕ → V)
    (chain : List ℕ)
    (hbase : IsThetaEigen theta epsilon (G 1))
    (hstep : ∀ m p, IsThetaEigen theta epsilon (G m) →
      IsThetaEigen theta epsilon (G (m * p))) :
    IsThetaEigen theta epsilon (G (chain.prod)) := by
  induction chain with
  | nil => simpa using hbase
  | cons p ps ih =>
      simpa [List.prod_cons, mul_comm] using hstep ps.prod p ih

/-- A concrete coefficient series with the exact normalization
`q^{-n/24} - a q^{1/24} + O(q^{25/24})`. -/
def normalizedHSeries {R : Type*} [Ring R]
    (n : ℕ) (a : R) (tail : ℤ → R) : HForm R :=
  fun r =>
    if r = -(n : ℤ) then 1
    else if r = 1 then -a
    else if 25 ≤ r then tail r else 0

/-- The concrete auxiliary series satisfies the complete `H_n`
normalization, including all low-coefficient vanishings. -/
theorem normalizedHSeries_hasHnNormalization
    {R : Type*} [Ring R]
    (n : ℕ) (a : R) (tail : ℤ → R) :
    HasHnNormalization n a (normalizedHSeries n a tail) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [normalizedHSeries]
  · have hne : (1 : ℤ) ≠ -(n : ℤ) := by omega
    simp [normalizedHSeries, hne]
  · intro r hr hrn hr1
    have hnot : ¬ 25 ≤ r := by omega
    simp [normalizedHSeries, hrn, hr1, hnot]

/-- The paper's auxiliary form in the coefficient model. -/
def paperHn {R : Type*} [Ring R]
    (n : ℕ) (a : R) (tail : ℤ → R) : HForm R :=
  normalizedHSeries n a tail

/-- The exact normalization theorem for `paperHn`. -/
theorem paperHn_normalization
    {R : Type*} [Ring R]
    (n : ℕ) (a : R) (tail : ℤ → R) :
    HasHnNormalization n a (paperHn n a tail) :=
  normalizedHSeries_hasHnNormalization n a tail

/-- Paper-specific name for the regularized pairing carried by finite-height
Stokes data.  The actual limit argument is `StokesPairingData.pairing_formula`. -/
def paperRegularizedPairing (d : StokesPairingData) : ℝ :=
  regularizedPairing d

@[simp] theorem paperRegularizedPairing_eq (d : StokesPairingData) :
    paperRegularizedPairing d = d.pairing := rfl

end SptCM.Analytic
