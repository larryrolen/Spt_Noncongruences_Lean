module

public import blessed.SptCM.Interfaces
public import blessed.SptCM.PaperInterfaces

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Oriented CM class polynomials

The arithmetic geometry used to construct CM points and prove integrality of
their Hauptmodul coordinates remains an external input.  Here we formalize
the algebraic deductions from the four finite orientation sets: products of
linear factors are monic, and the two pairs of orientations have degree twice
the class number.
-/

namespace SptCM

noncomputable section

open Polynomial
open PaperInterfaces

/-- An integral binary quadratic form `[a,b,c]`. -/
structure IntegralBinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ

/-- The raw oriented level-six forms of discriminant `-n`.  Passage to
`Γ₀(6)`-classes and the finiteness/cardinality theorem are external arithmetic
inputs, represented below by finite index types and cardinality hypotheses. -/
@[expose]
def rawOrientedForms (n r : ℕ) : Set IntegralBinaryQuadraticForm :=
  {Q | Q.b ^ 2 - 4 * Q.a * Q.c = -(n : ℤ) ∧ 0 < Q.a ∧
    (6 : ℤ) ∣ Q.a ∧ Q.b % 12 = (r : ℤ) % 12 ∧
    Nat.gcd (Nat.gcd Q.a.natAbs Q.b.natAbs) Q.c.natAbs = 1}

/-- An integral matrix in `Γ₀(6)`: determinant one and lower-left entry
divisible by six. -/
structure GammaZeroSixMatrix where
  p : ℤ
  q : ℤ
  s : ℤ
  t : ℤ
  determinant_one : p * t - q * s = 1
  lowerLeft_dvd : (6 : ℤ) ∣ s

/-- Change of variables of an integral binary quadratic form by a matrix
`((p,q),(s,t))`. -/
@[expose]
def transformQuadraticForm (g : GammaZeroSixMatrix)
    (Q : IntegralBinaryQuadraticForm) : IntegralBinaryQuadraticForm where
  a := Q.a * g.p ^ 2 + Q.b * g.p * g.s + Q.c * g.s ^ 2
  b := 2 * Q.a * g.p * g.q + Q.b * (g.p * g.t + g.q * g.s) +
    2 * Q.c * g.s * g.t
  c := Q.a * g.q ^ 2 + Q.b * g.q * g.t + Q.c * g.t ^ 2

/-- A raw oriented form, before quotienting by `Γ₀(6)`. -/
abbrev RawOrientedForm (n r : ℕ) := {Q // Q ∈ rawOrientedForms n r}

/-- The one-step `Γ₀(6)` change-of-variables relation on oriented forms. -/
@[expose]
def gammaZeroSixRelated (n r : ℕ)
    (Q Q' : RawOrientedForm n r) : Prop :=
  ∃ g : GammaZeroSixMatrix, transformQuadraticForm g Q.1 = Q'.1

/-- The oriented quadratic-form classes `𝒬_{n,r}`: primitive positive
definite forms of discriminant `-n`, with `6 ∣ a` and `b ≡ r (mod 12)`,
modulo `Γ₀(6)`. `EqvGen` packages the equivalence closure of the concrete
change-of-variables relation. -/
@[expose]
def orientedForms (n r : ℕ) : Type :=
  Quotient (Relation.EqvGen.setoid (gammaZeroSixRelated n r))

/-- The level-six eta quotient, parameterized by the analytic eta function.
This separates its algebraic formula from the cited modularity and integral
model results. -/
@[expose]
def hauptmodul (eta : ℂ → ℂ) (τ : ℂ) : ℂ :=
  eta τ ^ 5 * eta (3 * τ) / (eta (2 * τ) * eta (6 * τ) ^ 5)

/-- The exponent vector `(5,-1,1,-5)` of the level-six eta quotient
has weight zero. -/
theorem hauptmodul_exponent_sum :
    5 + (-1 : ℤ) + 1 + (-5) = 0 := by norm_num

/-- The first Ligozat congruence sum for the level-six eta quotient. -/
theorem hauptmodul_first_congruence_sum :
    1 * 5 + 2 * (-1 : ℤ) + 3 * 1 + 6 * (-5) = -24 := by norm_num

/-- The second Ligozat congruence sum for the level-six eta quotient. -/
theorem hauptmodul_second_congruence_sum :
    6 * 5 + 3 * (-1 : ℤ) + 2 * 1 + 1 * (-5) = 24 := by norm_num

/-- The standard degree-one criterion used in the integral-model argument.
It records the ambient modular curve and its integral geometry, rather than
building the full moduli stack in this paper-specific development. -/
structure IntegralCoordinateGeometry
    {Exponent Cusp Order Quotient : Type*}
    (M : EtaQuotientModel Exponent Cusp Order Quotient) where
  zeroCusp : Cusp
  infinityCusp : Cusp
  otherCusps : Set Cusp
  integralUnitExpansionAtInfinity : Quotient → Prop
  noInteriorZeros : Quotient → Prop
  identifiesWithProjectiveLine : Quotient → Prop
  degreeOneCriterion :
    ∀ (e : Exponent) (f : Quotient),
      f = M.quotient e →
      M.isWeightZeroModularFunction f →
      M.hasTrivialCharacter f →
      (∀ c : Cusp, M.cuspOrder f c = M.orderFormula e c) →
      (∀ c ∈ otherCusps, c ≠ zeroCusp ∧ c ≠ infinityCusp) →
      integralUnitExpansionAtInfinity f →
      noInteriorZeros f →
      identifiesWithProjectiveLine f

/-- Ligozat's formula and the integral `q`-expansion supply the hypotheses of
the degree-one integral-coordinate criterion.  In the concrete application,
the separately checked cusp orders are `1,0,0,-1`; these are exactly what
establishes `hnoInteriorZeros` and the degree-one divisor used by the
criterion. -/
theorem hauptmodul_integral_coordinate
    {Exponent Cusp Order Quotient : Type*}
    (M : EtaQuotientModel Exponent Cusp Order Quotient)
    (G : IntegralCoordinateGeometry M)
    (hLigozat : LigozatEtaQuotientInput M)
    (e : Exponent) (t : Quotient)
    (ht : M.quotient e = t) (hconditions : M.conditions e)
    (hcharacter : M.characterIsTrivial e)
    (hother : ∀ c ∈ G.otherCusps,
      c ≠ G.zeroCusp ∧ c ≠ G.infinityCusp)
    (hqexp : G.integralUnitExpansionAtInfinity t)
    (hnoInteriorZeros : G.noInteriorZeros t) :
    G.identifiesWithProjectiveLine t := by
  have hmodular := hLigozat e hconditions
  exact G.degreeOneCriterion e t ht.symm
    (ht ▸ hmodular.1) (ht ▸ hmodular.2.2 hcharacter)
    (fun c => ht ▸ hmodular.2.1 c) hother hqexp hnoInteriorZeros

/-- A chosen family really is a representative family when it meets every
class once.  This separates the finite choice of representatives from the raw
oriented-form predicate. -/
structure OrientedClassRepresentatives (n r : ℕ) (Class : Type*) where
  representative : Class → RawOrientedForm n r
  classMap : Class → orientedForms n r :=
    fun c => Quotient.mk'' (representative c)
  injective : Function.Injective classMap

section ClassPolynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The polynomial whose roots are a finite family of CM coordinates. -/
@[expose]
def classPolynomial {ι : Type*} [Fintype ι] (t : ι → R) : R[X] :=
  ∏ i, (X - C (t i))

/-- A class polynomial presented as a product of linear factors is monic. -/
theorem classPolynomial_monic {ι : Type*} [Fintype ι] (t : ι → R) :
    (classPolynomial t).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C (t i)

/-- Its degree is the number of coordinates, including multiplicity. -/
theorem classPolynomial_natDegree {ι : Type*} [Fintype ι] (t : ι → R) :
    (classPolynomial t).natDegree = Fintype.card ι := by
  classical
  simpa [classPolynomial] using
    (natDegree_finsetProd_X_sub_C_eq_card (R := R) (Finset.univ : Finset ι) t)

/-- Evaluation of a class polynomial vanishes exactly at one of its listed
coordinates, after scalar extension to a domain. -/
theorem aeval_classPolynomial_eq_zero_iff
    {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    {L : Type*} [CommRing L] [IsDomain L] [Algebra K L]
    (t : ι → K) (x : L) :
    aeval x (classPolynomial t) = 0 ↔
      ∃ i : ι, x = algebraMap K L (t i) := by
  classical
  simp only [classPolynomial, map_prod, map_sub, aeval_X, aeval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, sub_eq_zero.mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, sub_eq_zero.mpr hi⟩

/-- The numerator class polynomial formed from the orientations `1` and `11`. -/
@[expose]
def classPolyA
    {ι₁ ι₁₁ : Type*} [Fintype ι₁] [Fintype ι₁₁]
    (t₁ : ι₁ → R) (t₁₁ : ι₁₁ → R) : R[X] :=
  classPolynomial t₁ * classPolynomial t₁₁

/-- The denominator class polynomial formed from the orientations `5` and `7`. -/
@[expose]
def classPolyB
    {ι₅ ι₇ : Type*} [Fintype ι₅] [Fintype ι₇]
    (t₅ : ι₅ → R) (t₇ : ι₇ → R) : R[X] :=
  classPolynomial t₅ * classPolynomial t₇

/-- A root of the numerator comes from orientation `1` or `11`. -/
theorem aeval_classPolyA_eq_zero_iff
    {K : Type*} [Field K]
    {ι₁ ι₁₁ : Type*} [Fintype ι₁] [Fintype ι₁₁]
    {L : Type*} [CommRing L] [IsDomain L] [Algebra K L]
    (t₁ : ι₁ → K) (t₁₁ : ι₁₁ → K) (x : L) :
    aeval x (classPolyA t₁ t₁₁) = 0 ↔
      (∃ i : ι₁, x = algebraMap K L (t₁ i)) ∨
      (∃ i : ι₁₁, x = algebraMap K L (t₁₁ i)) := by
  simp [classPolyA, aeval_classPolynomial_eq_zero_iff]

/-- A root of the denominator comes from orientation `5` or `7`. -/
theorem aeval_classPolyB_eq_zero_iff
    {K : Type*} [Field K]
    {ι₅ ι₇ : Type*} [Fintype ι₅] [Fintype ι₇]
    {L : Type*} [CommRing L] [IsDomain L] [Algebra K L]
    (t₅ : ι₅ → K) (t₇ : ι₇ → K) (x : L) :
    aeval x (classPolyB t₅ t₇) = 0 ↔
      (∃ i : ι₅, x = algebraMap K L (t₅ i)) ∨
      (∃ i : ι₇, x = algebraMap K L (t₇ i)) := by
  simp [classPolyB, aeval_classPolynomial_eq_zero_iff]

/-- The numerator is monic. -/
theorem classPolyA_monic
    {ι₁ ι₁₁ : Type*} [Fintype ι₁] [Fintype ι₁₁]
    (t₁ : ι₁ → R) (t₁₁ : ι₁₁ → R) :
    (classPolyA t₁ t₁₁).Monic := by
  exact (classPolynomial_monic t₁).mul (classPolynomial_monic t₁₁)

/-- The denominator is monic. -/
theorem classPolyB_monic
    {ι₅ ι₇ : Type*} [Fintype ι₅] [Fintype ι₇]
    (t₅ : ι₅ → R) (t₇ : ι₇ → R) :
    (classPolyB t₅ t₇).Monic := by
  exact (classPolynomial_monic t₅).mul (classPolynomial_monic t₇)

/-- The exact degree calculation from the external ideal-class enumeration:
each of the two numerator orientation sets has cardinality `h`. -/
theorem classPolyA_natDegree
    {ι₁ ι₁₁ : Type*} [Fintype ι₁] [Fintype ι₁₁]
    (t₁ : ι₁ → R) (t₁₁ : ι₁₁ → R) (h : ℕ)
    (hcard₁ : Fintype.card ι₁ = h) (hcard₁₁ : Fintype.card ι₁₁ = h) :
    (classPolyA t₁ t₁₁).natDegree = 2 * h := by
  rw [classPolyA, (classPolynomial_monic t₁).natDegree_mul (classPolynomial_monic t₁₁),
    classPolynomial_natDegree, classPolynomial_natDegree, hcard₁, hcard₁₁]
  omega

/-- The analogous degree calculation for orientations `5` and `7`. -/
theorem classPolyB_natDegree
    {ι₅ ι₇ : Type*} [Fintype ι₅] [Fintype ι₇]
    (t₅ : ι₅ → R) (t₇ : ι₇ → R) (h : ℕ)
    (hcard₅ : Fintype.card ι₅ = h) (hcard₇ : Fintype.card ι₇ = h) :
    (classPolyB t₅ t₇).natDegree = 2 * h := by
  rw [classPolyB, (classPolynomial_monic t₅).natDegree_mul (classPolynomial_monic t₇),
    classPolynomial_natDegree, classPolynomial_natDegree, hcard₅, hcard₇]
  omega

/-- Combined arithmetic package: both oriented class polynomials are monic
and both have degree `2h`.  The only arithmetic-geometric inputs are the four
cardinality equalities. -/
theorem classPolynomials_arithmetic
    {ι₁ ι₁₁ ι₅ ι₇ : Type*}
    [Fintype ι₁] [Fintype ι₁₁] [Fintype ι₅] [Fintype ι₇]
    (t₁ : ι₁ → R) (t₁₁ : ι₁₁ → R)
    (t₅ : ι₅ → R) (t₇ : ι₇ → R) (h : ℕ)
    (hcard₁ : Fintype.card ι₁ = h) (hcard₁₁ : Fintype.card ι₁₁ = h)
    (hcard₅ : Fintype.card ι₅ = h) (hcard₇ : Fintype.card ι₇ = h) :
    (classPolyA t₁ t₁₁).Monic ∧ (classPolyB t₅ t₇).Monic ∧
      (classPolyA t₁ t₁₁).natDegree = 2 * h ∧
      (classPolyB t₅ t₇).natDegree = 2 * h := by
  exact ⟨classPolyA_monic t₁ t₁₁, classPolyB_monic t₅ t₇,
    classPolyA_natDegree t₁ t₁₁ h hcard₁ hcard₁₁,
    classPolyB_natDegree t₅ t₇ h hcard₅ hcard₇⟩

/-- Consequently the two oriented class polynomials have equal degree. -/
theorem orientedClassPolynomials_equal_natDegree
    {ι₁ ι₁₁ ι₅ ι₇ : Type*}
    [Fintype ι₁] [Fintype ι₁₁] [Fintype ι₅] [Fintype ι₇]
    (t₁ : ι₁ → R) (t₁₁ : ι₁₁ → R)
    (t₅ : ι₅ → R) (t₇ : ι₇ → R) (h : ℕ)
    (hcard₁ : Fintype.card ι₁ = h) (hcard₁₁ : Fintype.card ι₁₁ = h)
    (hcard₅ : Fintype.card ι₅ = h) (hcard₇ : Fintype.card ι₇ = h) :
    (classPolyA t₁ t₁₁).natDegree =
      (classPolyB t₅ t₇).natDegree := by
  rw [classPolyA_natDegree t₁ t₁₁ h hcard₁ hcard₁₁,
    classPolyB_natDegree t₅ t₇ h hcard₅ hcard₇]

end ClassPolynomial

end

end SptCM
