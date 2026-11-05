module

public import blessed.SptCM.Analytic.DualityPairing
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# The triangular eta--j construction of the auxiliary forms

The external input in this file is only the standard unitriangular Fourier
expansion of the powers `η j^d`, together with their modular qualification.
The polynomial selecting the paper's prescribed principal part is constructed
by inverting that integral unitriangular coefficient matrix.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic Polynomial Matrix
open scoped BigOperators

/-- Standard E4 data for the integral Fourier expansions of `η j^d`.
The index `r` is the numerator in `q^(r/24)`.  The final field is the usual
support statement for eta times a polynomial in `j`, not a paper-specific
normalization. -/
structure EtaJPowerBasis (Form : Type*) where
  powerForm : ℕ → Form
  polynomialForm : Polynomial ℤ → Form
  coefficients : Form → HForm ℤ
  qualifies : Form → Prop
  polynomial_qualifies : ∀ P, qualifies (polynomialForm P)
  polynomial_coefficients : ∀ k (c : Fin (k + 1) → ℤ) r,
    coefficients (polynomialForm
      (∑ d : Fin (k + 1), Polynomial.monomial (d : ℕ) (c d))) r =
      ∑ d : Fin (k + 1), c d * coefficients (powerForm d) r
  leading : ∀ d, coefficients (powerForm d) (1 - 24 * (d : ℤ)) = 1
  triangular : ∀ d i, d < i →
    coefficients (powerForm d) (1 - 24 * (i : ℤ)) = 0
  support : ∀ d r, r < 25 →
    (∀ i : ℕ, r ≠ 1 - 24 * (i : ℤ)) →
      coefficients (powerForm d) r = 0

/-- The unitriangular coefficient matrix of
`η, ηj, ..., ηj^k`, ordered by the exponents `q^(1/24), q^(-23/24), ...`. -/
@[expose]
def etaJMatrix {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i d => E.coefficients (E.powerForm d) (1 - 24 * (i : ℤ))

lemma etaJMatrix_upperTriangular {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) :
    (etaJMatrix E k).IsUpperTriangular := by
  intro i d hid
  exact E.triangular d i hid

@[simp] lemma etaJMatrix_diag {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (i : Fin (k + 1)) :
    etaJMatrix E k i i = 1 := by
  exact E.leading i

lemma etaJMatrix_det {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) :
    (etaJMatrix E k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (etaJMatrix_upperTriangular E k)]
  simp

/-- Desired coefficients at the triangular exponents.  The top entry is the
monic leading term, the bottom entry is `-a(n)`, and all intermediate negative
terms vanish. -/
@[expose]
def hnTarget (k : ℕ) (a : ℤ) : Fin (k + 1) → ℤ :=
  fun i => if (i : ℕ) = k then 1 else if (i : ℕ) = 0 then -a else 0

/-- The integral coefficient vector obtained by solving the unitriangular
eta--j system. -/
@[expose]
noncomputable def triangularCoefficients {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Fin (k + 1) → ℤ :=
  (etaJMatrix E k)⁻¹ *ᵥ hnTarget k a

lemma etaJMatrix_mulVec_triangularCoefficients {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    etaJMatrix E k *ᵥ triangularCoefficients E k a = hnTarget k a := by
  let hunit : IsUnit (etaJMatrix E k).det := by
    rw [etaJMatrix_det]
    exact isUnit_one
  rw [triangularCoefficients, Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _ hunit]
  exact Matrix.one_mulVec _

/-- The integral polynomial supplied by triangular elimination. -/
@[expose]
noncomputable def triangularPolynomial {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Polynomial ℤ :=
  ∑ d : Fin (k + 1), Polynomial.monomial (d : ℕ) (triangularCoefficients E k a d)


@[simp] lemma triangularPolynomial_coeff {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) (d : Fin (k + 1)) :
    (triangularPolynomial E k a).coeff d = triangularCoefficients E k a d := by
  rw [triangularPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    have hnat : (d : ℕ) ≠ (b : ℕ) := by
      intro h
      apply hbd
      exact Fin.ext h.symm
    simp [Polynomial.coeff_monomial, Ne.symm hnat]
  · simp

lemma triangularPolynomial_coeff_eq_zero {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) (d : ℕ)
    (hd : k < d) :
    (triangularPolynomial E k a).coeff d = 0 := by
  rw [triangularPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro b _
  have hne : d ≠ (b : ℕ) := by omega
  simp [Polynomial.coeff_monomial, Ne.symm hne]

lemma triangularPolynomial_coeff_top {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    (triangularPolynomial E k a).coeff k = 1 := by
  let top : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hsolve := congrFun (etaJMatrix_mulVec_triangularCoefficients E k a) top
  have hrow :
      (etaJMatrix E k *ᵥ triangularCoefficients E k a) top =
        triangularCoefficients E k a top := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single top]
    · simp [etaJMatrix_diag]
    · intro d _ hdt
      have hdk : (d : ℕ) < k := by
        have hle : (d : ℕ) ≤ k := Nat.le_of_lt_succ d.isLt
        exact lt_of_le_of_ne hle (by
          intro h
          apply hdt
          apply Fin.ext
          simpa using h)
      simp [etaJMatrix, E.triangular d top hdk]
    · simp
  rw [hrow] at hsolve
  have hcoeff : triangularCoefficients E k a top = 1 := by
    simpa [hnTarget, top] using hsolve
  change (triangularPolynomial E k a).coeff (top : ℕ) = 1
  rw [triangularPolynomial_coeff]
  exact hcoeff

lemma triangularPolynomial_monic {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    (triangularPolynomial E k a).Monic := by
  let p : Polynomial.MonicDegreeEq ℤ k :=
    ⟨triangularPolynomial E k a, triangularPolynomial_coeff_top E k a,
      fun d hd => triangularPolynomial_coeff_eq_zero E k a d hd⟩
  exact p.monic

/-- The actual form `η P_k(j)` selected by triangular elimination. -/
@[expose]
noncomputable def auxiliaryForm {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Form :=
  E.polynomialForm (triangularPolynomial E k a)

/-- The coefficient series of the source-faithful auxiliary form. -/
@[expose]
noncomputable def auxiliaryHn {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : HForm ℤ :=
  E.coefficients (auxiliaryForm E k a)

lemma auxiliaryHn_triangular_coefficient {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) (i : Fin (k + 1)) :
    auxiliaryHn E k a (1 - 24 * (i : ℤ)) = hnTarget k a i := by
  have hsolve := congrFun (etaJMatrix_mulVec_triangularCoefficients E k a) i
  rw [auxiliaryHn, auxiliaryForm, triangularPolynomial, E.polynomial_coefficients]
  simpa [etaJMatrix, Matrix.mulVec, dotProduct, mul_comm] using hsolve

lemma auxiliaryHn_leading {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    auxiliaryHn E k a (1 - 24 * (k : ℤ)) = 1 := by
  simpa [hnTarget] using
    auxiliaryHn_triangular_coefficient E k a
      (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))

/-- The first positive coefficient is fixed during the same triangular solve;
it is not an extra field of the eta--j input. -/
lemma auxiliaryHn_first_coefficient {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (hk : 0 < k) (a : ℤ) :
    auxiliaryHn E k a 1 = -a := by
  simpa [hnTarget, Nat.ne_of_lt hk] using
    auxiliaryHn_triangular_coefficient E k a
      (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))

lemma auxiliaryHn_low_coefficient {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) (r : ℤ)
    (hr : r < 25) (hrtop : r ≠ 1 - 24 * (k : ℤ)) (hrone : r ≠ 1) :
    auxiliaryHn E k a r = 0 := by
  rw [auxiliaryHn, auxiliaryForm, triangularPolynomial, E.polynomial_coefficients]
  by_cases hshape : ∃ i : ℕ, r = 1 - 24 * (i : ℤ)
  · obtain ⟨i, rfl⟩ := hshape
    by_cases hik : i ≤ k
    · let fi : Fin (k + 1) := ⟨i, Nat.lt_succ_iff.mpr hik⟩
      have hrow := auxiliaryHn_triangular_coefficient E k a fi
      rw [auxiliaryHn, auxiliaryForm, triangularPolynomial,
        E.polynomial_coefficients] at hrow
      have hi0 : i ≠ 0 := by
        intro hi
        subst hi
        simp at hrone
      have hik' : i ≠ k := by
        intro hi
        subst hi
        exact hrtop rfl
      simpa [auxiliaryHn, auxiliaryForm, E.polynomial_coefficients,
        hnTarget, fi, hi0, hik'] using hrow
    · apply Finset.sum_eq_zero
      intro d _
      have hdi : (d : ℕ) < i := by omega
      simp [E.triangular d i hdi]
  · apply Finset.sum_eq_zero
    intro d _
    simp [E.support d r hr (by simpa using hshape)]

/-- I07: the triangularly constructed eta--j form has exactly the paper's
Fourier normalization. -/
theorem auxiliaryHn_normalization {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (hk : 0 < k) (a : ℤ) :
    HasHnNormalization (24 * k - 1) a (auxiliaryHn E k a) := by
  have hindex : -((24 * k - 1 : ℕ) : ℤ) = 1 - 24 * (k : ℤ) := by omega
  refine ⟨?_, auxiliaryHn_first_coefficient E k hk a, ?_⟩
  · rw [hindex]
    exact auxiliaryHn_leading E k a
  · intro r hr hrn hr1
    apply auxiliaryHn_low_coefficient E k a r hr
    · simpa [hindex] using hrn
    · exact hr1

/-- The actual eta--j form satisfies the general modular qualification from
E4; only the polynomial selection and normalization are internal. -/
theorem auxiliaryForm_qualifies {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    E.qualifies (auxiliaryForm E k a) :=
  E.polynomial_qualifies _

/-- A polynomial has the prescribed triangular eta--j coefficients through
its leading exponent. -/
@[expose]
def HasTriangularNormalization {Form : Type*} (E : EtaJPowerBasis Form)
    (k : ℕ) (a : ℤ) (P : Polynomial ℤ) : Prop :=
  P.natDegree ≤ k ∧ ∀ i : Fin (k + 1),
    E.coefficients (E.polynomialForm P) (1 - 24 * (i : ℤ)) = hnTarget k a i

lemma polynomial_eq_fin_monomial_sum {k : ℕ} (P : Polynomial ℤ)
    (hdeg : P.natDegree ≤ k) :
    P = ∑ d : Fin (k + 1), Polynomial.monomial (d : ℕ) (P.coeff d) := by
  ext n
  by_cases hn : n < k + 1
  · let d : Fin (k + 1) := ⟨n, hn⟩
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single d]
    · simp [d]
    · intro b _ hbd
      have hne : (b : ℕ) ≠ n := by
        intro h
        apply hbd
        apply Fin.ext
        simpa [d] using h
      simp [Polynomial.coeff_monomial, hne]
    · simp
  · have hkn : k < n := by omega
    have hzero : P.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hkn)
    rw [hzero, Polynomial.finsetSum_coeff]
    symm
    apply Finset.sum_eq_zero
    intro d _
    have hne : (d : ℕ) ≠ n := by omega
    simp [Polynomial.coeff_monomial, hne]

lemma hasTriangularNormalization_triangularPolynomial {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    HasTriangularNormalization E k a (triangularPolynomial E k a) := by
  constructor
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun d hd =>
      triangularPolynomial_coeff_eq_zero E k a d hd
  · intro i
    simpa [auxiliaryHn, auxiliaryForm] using
      auxiliaryHn_triangular_coefficient E k a i

/-- I07 triangular elimination: there is a unique integral polynomial of
degree at most `k` whose eta--j expansion has the prescribed leading term,
vanishing intermediate terms, and first coefficient `-a`.  The constructed
polynomial is monic. -/
theorem existsUnique_triangularPolynomial {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) :
    ∃! P : Polynomial ℤ,
      P.Monic ∧ HasTriangularNormalization E k a P := by
  refine ⟨triangularPolynomial E k a,
    ⟨triangularPolynomial_monic E k a,
      hasTriangularNormalization_triangularPolynomial E k a⟩, ?_⟩
  intro P hP
  have hrepr := polynomial_eq_fin_monomial_sum P hP.2.1
  let cP : Fin (k + 1) → ℤ := fun d => P.coeff d
  have hmul : etaJMatrix E k *ᵥ cP = hnTarget k a := by
    funext i
    have hi := hP.2.2 i
    rw [hrepr, E.polynomial_coefficients] at hi
    simpa [etaJMatrix, Matrix.mulVec, dotProduct, cP, mul_comm] using hi
  have hc : cP = triangularCoefficients E k a := by
    apply Matrix.mulVec_injective_of_isUnit (A := etaJMatrix E k)
      ((Matrix.isUnit_iff_isUnit_det _).2 (by
        rw [etaJMatrix_det]
        exact isUnit_one))
    rw [hmul, etaJMatrix_mulVec_triangularCoefficients]
  rw [hrepr, triangularPolynomial]
  apply Finset.sum_congr rfl
  intro d _
  rw [show P.coeff d = triangularCoefficients E k a d by
    exact congrFun hc d]


/-- The one-index specification of the internally constructed auxiliary form:
qualification comes from the general eta--j theorem, while monicity and the
Fourier normalization are proved by the triangular solve. -/
@[expose]
def AuxiliaryFormSpec {Form : Type*} (E : EtaJPowerBasis Form)
    (k : ℕ) (a : ℤ) : Prop :=
  E.qualifies (auxiliaryForm E k a) ∧
    (triangularPolynomial E k a).Monic ∧
      HasHnNormalization (24 * k - 1) a (auxiliaryHn E k a)

/-- I07: the actual form `η P_{24k-1}(j)` satisfies the complete auxiliary
form specification for every positive `k`. -/
theorem auxiliaryForm_spec {Form : Type*}
    (E : EtaJPowerBasis Form) (k : ℕ) (hk : 0 < k) (a : ℤ) :
    AuxiliaryFormSpec E k a := by
  exact ⟨auxiliaryForm_qualifies E k a,
    triangularPolynomial_monic E k a,
    auxiliaryHn_normalization E k hk a⟩

end SptCM.Analytic.Repaired
