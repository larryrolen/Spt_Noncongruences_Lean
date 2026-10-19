import blessed.SptCM.Analytic.Repaired.GaussSum
import blessed.SptCM.Analytic.Repaired.AuxiliaryForms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact level-twelve Weil-generator calculation

This file records the two finite matrix calculations for the component vector
`e₁ - e₅ - e₇ + e₁₁`.  It does not postulate a Weil law: the `S` equation is
the verified Gauss sum and the `T` equation is a twelve-case calculation.
-/

namespace SptCM.Analytic.Repaired

open scoped BigOperators

/-- The component vector `c (e₁ - e₅ - e₇ + e₁₁)`, evaluated on the
canonical representatives of `ℤ / 12ℤ`. -/
def fourComponentVector (c : ℂ) (r : Fin 12) : ℂ :=
  c * (chiTwelveResidue r : ℂ)

/-- The normalized finite Fourier matrix giving the level-twelve Weil
`S`-generator, with the same inverse-root convention as the Gauss sum. -/
noncomputable def levelTwelveWeilS (x : Fin 12 → ℂ) (s : Fin 12) : ℂ :=
  (Real.sqrt 12 : ℂ)⁻¹ *
    ∑ r : Fin 12, inverseTwelfthRoot ^ ((r.val * s.val) % 12) * x r

/-- The common `T` multiplier of the four supported components. -/
noncomputable def levelTwelveTMultiplier : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 12 : ℂ))

/-- The diagonal level-twelve Weil `T`-generator.  The exponent is the
quadratic residue `r² mod 24`; all four supported indices have residue one. -/
noncomputable def levelTwelveWeilT (x : Fin 12 → ℂ) (r : Fin 12) : ℂ :=
  levelTwelveTMultiplier ^ ((r.val ^ 2) % 24) * x r


private def levelTwelveResidues : Finset (Fin 12) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}

private theorem levelTwelveResidues_eq_univ :
    levelTwelveResidues = Finset.univ := by
  decide

set_option maxRecDepth 10000 in
private theorem fourComponent_fourier_sum (c : ℂ) (s : Fin 12) :
    (∑ r : Fin 12,
      inverseTwelfthRoot ^ ((r.val * s.val) % 12) *
        fourComponentVector c r) =
      c * chiTwelveGaussSum s := by
  rw [← levelTwelveResidues_eq_univ]
  simp [levelTwelveResidues, fourComponentVector, chiTwelveGaussSum,
    chiTwelveResidue, Fin.ext_iff]
  rw [Nat.mod_eq_of_lt s.isLt]
  ring

private theorem sqrt_twelve_ne_zero : (Real.sqrt 12 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 12)).ne'

/-- Exact `S`-generator calculation for the four-component vector. -/
theorem fourComponentVector_weilS (c : ℂ) :
    levelTwelveWeilS (fourComponentVector c) = fourComponentVector c := by
  funext s
  rw [levelTwelveWeilS, fourComponent_fourier_sum,
    chiTwelve_gauss_sum]
  field_simp [sqrt_twelve_ne_zero]
  simp [fourComponentVector]

/-- Exact `T`-generator calculation for the four-component vector. -/
theorem fourComponentVector_weilT (c : ℂ) :
    levelTwelveWeilT (fourComponentVector c) =
      fun r => levelTwelveTMultiplier * fourComponentVector c r := by
  funext r
  fin_cases r <;>
    simp [levelTwelveWeilT, fourComponentVector, chiTwelveResidue,
      Fin.ext_iff]

/-- I10: the fixed four-component vector has exactly the `S` and `T`
transformations required at level twelve.  This is the paired matrix identity,
not an abstract implication from caller-supplied generator statements. -/
theorem fourComponentVector_weil_generators (c : ℂ) :
    levelTwelveWeilS (fourComponentVector c) = fourComponentVector c ∧
    levelTwelveWeilT (fourComponentVector c) =
      fun r => levelTwelveTMultiplier * fourComponentVector c r :=
  ⟨fourComponentVector_weilS c, fourComponentVector_weilT c⟩


/-! ## Exact scalar eta--j input and the actual vector-valued form -/

/-- Exact E4 generator data for eta times an integral polynomial in `j`.
The two displayed equalities are the standard scalar `S`- and `T`-laws;
they are required for every polynomial, rather than merely recorded as an
opaque qualification predicate. -/
structure EtaJGeneratorBasis (Form : Type*) [SMul ℂ Form]
    extends EtaJPowerBasis Form where
  slashS : Form → Form
  slashT : Form → Form
  polynomial_slashS : ∀ P : Polynomial ℤ,
    slashS (polynomialForm P) = polynomialForm P
  polynomial_slashT : ∀ P : Polynomial ℤ,
    slashT (polynomialForm P) =
      levelTwelveTMultiplier • polynomialForm P

/-- The actual separated vector-valued input: its scalar form and its integral
Fourier series are fixed simultaneously.  Its finite component vector is the
canonical `e₁-e₅-e₇+e₁₁`, not caller-supplied data. -/
structure FourComponentInput (Form : Type*) where
  scalarForm : Form
  scalarSeries : HForm ℤ

/-- The concrete I10 input obtained from the triangular eta--j construction. -/
noncomputable def auxiliaryFourComponentInput {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (k : ℕ) (a : ℤ) :
    FourComponentInput Form where
  scalarForm := auxiliaryForm E.toEtaJPowerBasis k a
  scalarSeries := auxiliaryHn E.toEtaJPowerBasis k a

/-- The combined scalar/finite `S` equation.  The left side applies the
analytic slash action to the scalar form; the right side applies the exact
level-twelve Weil matrix to its fixed finite component. -/
def HasFourComponentWeilS {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  (E.slashS F.scalarForm, fourComponentVector 1) =
    (F.scalarForm, levelTwelveWeilS (fourComponentVector 1))

/-- The combined scalar/finite `T` equation, with the common multiplier
`e(1/24)` shown on the opposite tensor factor on the two sides. -/
def HasFourComponentWeilT {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  (E.slashT F.scalarForm,
      fun r => levelTwelveTMultiplier * fourComponentVector 1 r) =
    (levelTwelveTMultiplier • F.scalarForm,
      levelTwelveWeilT (fourComponentVector 1))

/-- Exact level-twelve Weil-generator law for a separated four-component
input.  Both equalities simultaneously contain the scalar eta--j law and the
finite matrix calculation. -/
def HasFourComponentWeilGeneratorLaw {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  HasFourComponentWeilS E F ∧ HasFourComponentWeilT E F

/-- I10: the actual `H_n = eta P_n(j)` together with
`e₁-e₅-e₇+e₁₁` obeys both Weil-generator transformations.  This theorem uses
the exact general E4 scalar eta--j equations and the internally evaluated
finite matrices; neither desired generator equation is a hypothesis. -/
theorem auxiliaryHn_weil_generators {Form : Type*} [SMul ℂ Form]
    (E : EtaJGeneratorBasis Form) (k : ℕ) (a : ℤ) :
    HasFourComponentWeilGeneratorLaw E
      (auxiliaryFourComponentInput E k a) := by
  constructor
  · apply Prod.ext
    · exact E.polynomial_slashS (triangularPolynomial E.toEtaJPowerBasis k a)
    · exact (fourComponentVector_weilS 1).symm
  · apply Prod.ext
    · exact E.polynomial_slashT (triangularPolynomial E.toEtaJPowerBasis k a)
    · exact (fourComponentVector_weilT 1).symm

end SptCM.Analytic.Repaired
