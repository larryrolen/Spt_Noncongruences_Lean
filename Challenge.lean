module
public import Mathlib
/-!# Conditional classification of smallest-parts congruences
The hypotheses below are explicit literature and geometric inputs.
E8 includes additional unproved application assumptions; exact literature
support for its oriented CM and integral reduction interfaces is not certified. This
statement does not claim that those inputs have been constructed in Lean.
The smallest-parts function is defined directly from integer partitions.
-/
@[expose] public section
  -- Preserve the standard ring operations when importing the complete Mathlib surface.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
namespace SptCM.Analytic
/-- The quadratic character `χ₁₂(m) = (12/m)`, explicitly by residue class. -/ def chi12 (m : ℤ) : ℤ := if m % 12 = 1 ∨ m % 12 = 11 then 1 else if m % 12 = 5 ∨ m % 12 = 7 then -1 else 0
end SptCM.Analytic
namespace Nat
/-- The least nonnegative representative of the Bézout coefficient of `a` modulo `n`. When `a` and `n` are coprime and `n` is positive, this is the multiplicative inverse of `a` modulo `n`. This compatibility definition supplies the conventional `Nat.modInv` name, which is not present in the Mathlib revision used by this project. -/ def modInv (a n : ℕ) : ℕ :=
  (gcdA a n % (n : ℤ)).toNat
end Nat
namespace SptCM
/-- The multiplicity of the least part of a partition. The unique partition of zero has no parts and is assigned weight zero. -/ def smallestPartMultiplicity {n : ℕ} (p : Nat.Partition n) : ℕ := if h : p.parts.toFinset.Nonempty then p.parts.count (p.parts.toFinset.min' h) else 0
/-- Andrews' smallest-parts function: the total number of occurrences of the smallest part among all partitions of `n`. -/ def spt (n : ℕ) : ℕ := ∑ p : Nat.Partition n, smallestPartMultiplicity p
/-- The canonical residue `b_ℓ`, represented by the inverse of 24 modulo `ℓ`. For primes `ℓ ≥ 5`, this lies in `{1, ..., ℓ - 1}`. -/ def canonicalResidue (ℓ : ℕ) : ℕ := Nat.modInv 24 ℓ
/-- A canonical congruence prime for `spt`: a prime `ℓ ≥ 5` for which the canonical progression is identically zero modulo `ℓ`. -/ def CanonicalCongruencePrime (ℓ : ℕ) : Prop := ℓ.Prime ∧ 5 ≤ ℓ ∧ ∀ n : ℕ, ℓ ∣ spt (ℓ * n + canonicalResidue ℓ)
end SptCM
namespace SptCM.PaperInterfaces
/-- A coefficient model for a Laurent or fractional-power series. The index normalization (for example, exponents `n / 24`) is carried by the consumer. -/ abbrev CoeffSeries (R : Type*) := ℤ → R
/-- A coefficientwise operator on the neutral series model. -/ abbrev SeriesOperator (R : Type*) := CoeffSeries R → CoeffSeries R
/-- Ahlgren--Kim Proposition 6 after choosing the scalar normalization but before taking coefficientwise consequences. -/ def AhlgrenKimThetaCycleInput (ℓ : ℕ) (thetaPower : SeriesOperator (ZMod ℓ)) (epsilon : ZMod ℓ) (f : CoeffSeries (ZMod ℓ)) : Prop := thetaPower f = epsilon • f
end SptCM.PaperInterfaces
namespace SptCM.Analytic
section CoefficientModels
/-- A coefficient model for the fractional-power `q`-series in Section 2; the integer key is the numerator of the exponent `n/24`. -/ abbrev QSeries (K : Type*) := ℤ → K
/-- The principal-part predicate characterizing the canonical grid form. It states only the two negative coefficients used in the paper and vanishing of all other negative coefficients. -/ def HasGridPrincipalPart {K : Type*} [Ring K] (chi : ℕ → K) (m : ℕ) (g : QSeries K) : Prop :=
  ∀ r : ℤ, r < 0 → g r = if r = -(m : ℤ) ^ 2 then 1 else if r = -1 then -chi m else 0
/-- The coefficient formula for the paper's weight `3/2` Hecke operator. Inadmissible divided indices contribute zero. -/ def heckeThreeHalf {K : Type*} [Field K] (ell : ℕ) (chiEll : K) (legendre : ℤ → K) (g : QSeries K) : QSeries K := fun n => g (((ell : ℤ) ^ 2) * n) + chiEll * legendre (-n) * g n + if ((ell : ℤ) ^ 2) ∣ n then (ell : K) * g (n / (ell : ℤ) ^ 2) else 0
end CoefficientModels
end SptCM.Analytic
namespace SptCM.Analytic
open SptCM.PaperInterfaces
/-- The ordinary partition number, using Mathlib's finite type of partitions. -/ def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)
/-- The coefficient `a(r)` of the smallest-parts mock modular form. The supported nonnegative indices satisfy `r ≡ 23 (mod 24)` and correspond to `r = 24n - 1`; the principal coefficient at `r = -1` is specified separately. -/ def aCoeff (r : ℤ) : ℤ :=
  if r = -1 then 1
  else
    if 0 ≤ r ∧ r % 24 = 23 then
      let n := ((r + 1).toNat / 24)
      (-12 : ℤ) * (SptCM.spt n : ℤ) - r * (partitionNumber n : ℤ)
    else 0
/-- The coefficient-function model of `f = Σ a(r) q^(r/24)`. -/ def fSeries : QSeries ℤ := aCoeff
/-- Coefficientwise reduction of `f` modulo `ℓ`. -/ def fSeriesMod (ℓ : ℕ) : QSeries (ZMod ℓ) := fun r => (aCoeff r : ZMod ℓ)
/-- `Θ = q d/dq` on series indexed by the numerator of `r/24`. Accordingly, the coefficient at index `r` is multiplied by `r/24`. -/ def thetaSeriesOp (ℓ : ℕ) [Fact ℓ.Prime] : QSeries (ZMod ℓ) → QSeries (ZMod ℓ) := fun g r => ((r : ZMod ℓ) / (24 : ZMod ℓ)) * g r
/-- The coefficientwise closed form of the `k`-fold theta operator. -/ def thetaPowerSeriesOp (ℓ k : ℕ) [Fact ℓ.Prime] : QSeries (ZMod ℓ) → QSeries (ZMod ℓ) := fun g r => (((r : ZMod ℓ) / (24 : ZMod ℓ)) ^ k) * g r
/-- The `U_ℓ` operator on the integral-index coefficient model. -/ def uSeriesOp {R : Type*} (ℓ : ℕ) (g : QSeries R) : QSeries R := fun r => g ((ℓ : ℤ) * r)
/-- The scalar `(-24/ℓ)` appearing in the theta-cycle theorem. -/ def thetaCycleEigenvalue (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ := (legendreSym ℓ (-24) : ℤ)
/-- The precise conditional form of the Ahlgren--Kim input consumed by the paper: reduced `U_ℓ`-vanishing implies the stated theta-cycle eigenrelation. -/ def AhlgrenKimThetaCycleFromUInput (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  uSeriesOp ℓ (fSeriesMod ℓ) = 0 → PaperInterfaces.AhlgrenKimThetaCycleInput ℓ (thetaPowerSeriesOp ℓ ((ℓ - 1) / 2)) (thetaCycleEigenvalue ℓ) (fSeriesMod ℓ)
end SptCM.Analytic
namespace SptCM.Analytic
open Filter Polynomial
open scoped Topology BigOperators
/-- Coefficient model for the auxiliary weakly holomorphic form `H_n`. -/ abbrev HForm (R : Type*) := ℤ → R
section ClassPolynomials
variable {R ι κ : Type*} [CommRing R]
end ClassPolynomials
end SptCM.Analytic
namespace SptCM.Analytic.Repaired
open SptCM.Analytic Polynomial Matrix
open scoped BigOperators
/-- Standard E4 data for the integral Fourier expansions of `η j^d`. The index `r` is the numerator in `q^(r/24)`. The final field is the usual support statement for eta times a polynomial in `j`, not a paper-specific normalization. -/ structure EtaJPowerBasis (Form : Type*) where
  powerForm : ℕ → Form
  polynomialForm : Polynomial ℤ → Form
  coefficients : Form → HForm ℤ
  qualifies : Form → Prop
  polynomial_qualifies : ∀ P, qualifies (polynomialForm P)
  polynomial_coefficients : ∀ k (c : Fin (k + 1) → ℤ) r, coefficients (polynomialForm (∑ d : Fin (k + 1), Polynomial.monomial (d : ℕ) (c d))) r = ∑ d : Fin (k + 1), c d * coefficients (powerForm d) r
  leading : ∀ d, coefficients (powerForm d) (1 - 24 * (d : ℤ)) = 1
  triangular : ∀ d i, d < i → coefficients (powerForm d) (1 - 24 * (i : ℤ)) = 0
  support : ∀ d r, r < 25 → (∀ i : ℕ, r ≠ 1 - 24 * (i : ℤ)) → coefficients (powerForm d) r = 0
/-- The unitriangular coefficient matrix of `η, ηj, ..., ηj^k`, ordered by the exponents `q^(1/24), q^(-23/24), ...`. -/ def etaJMatrix {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ := fun i d => E.coefficients (E.powerForm d) (1 - 24 * (i : ℤ))
/-- Desired coefficients at the triangular exponents. The top entry is the monic leading term, the bottom entry is `-a(n)`, and all intermediate negative terms vanish. -/ def hnTarget (k : ℕ) (a : ℤ) : Fin (k + 1) → ℤ := fun i => if (i : ℕ) = k then 1 else if (i : ℕ) = 0 then -a else 0
/-- The integral coefficient vector obtained by solving the unitriangular eta--j system. -/ noncomputable def triangularCoefficients {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Fin (k + 1) → ℤ := (etaJMatrix E k)⁻¹ *ᵥ hnTarget k a
/-- The integral polynomial supplied by triangular elimination. -/ noncomputable def triangularPolynomial {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Polynomial ℤ := ∑ d : Fin (k + 1), Polynomial.monomial (d : ℕ) (triangularCoefficients E k a d)
/-- The actual form `η P_k(j)` selected by triangular elimination. -/ noncomputable def auxiliaryForm {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : Form := E.polynomialForm (triangularPolynomial E k a)
/-- The coefficient series of the source-faithful auxiliary form. -/ noncomputable def auxiliaryHn {Form : Type*} (E : EtaJPowerBasis Form) (k : ℕ) (a : ℤ) : HForm ℤ := E.coefficients (auxiliaryForm E k a)
end SptCM.Analytic.Repaired
namespace SptCM.RolenLiterature
open SptCM.Analytic
/-- Exact E4 boundary for the published Ahlgren--Kim modular grid. The record carries the fixed grid, its multiplier, the modular qualification, the two-term negative principal part in the published range, and uniqueness in that same range. Thus positive Fourier coefficients are data of the published family rather than a freely chosen tail. -/ structure AhlgrenKimGridTheorem (K : Type*) [Field K] where
  chi : ℕ → K
  chi_eq_chi12 : ∀ m, chi m = (SptCM.Analytic.chi12 m : K)
  grid : ℕ → QSeries K
  Qualifies : ℕ → QSeries K → Prop
  grid_one : grid 1 = 0
  qualifies_grid : ∀ m, 1 < m → Nat.Coprime m 6 → Qualifies m (grid m)
  principalPart : ∀ m, 1 < m → Nat.Coprime m 6 → HasGridPrincipalPart chi m (grid m)
  unique : ∀ m, 1 < m → Nat.Coprime m 6 → ∀ g, Qualifies m g → HasGridPrincipalPart chi m g → g = grid m
/-- The exact data-bearing published-grid result, rather than an opaque proposition saying merely that some grid has been published. -/ abbrev PublishedMockModularGrid (K : Type*) [Field K] := AhlgrenKimGridTheorem K
end SptCM.RolenLiterature
namespace SptCM.RolenLiterature
open CongruenceSubgroup
/-- The Möbius action of the integral congruence subgroup on the rational projective line. -/ local instance gammaZeroAction (N : ℕ) : MulAction (Gamma0 N) (OnePoint ℚ) := MulAction.compHom (OnePoint ℚ) ((Matrix.SpecialLinearGroup.mapGL ℚ).comp (Gamma0 N).subtype)
/-- Cusps of `X₀(N)`, represented as `Γ₀(N)`-orbits in `ℙ¹(ℚ)`. -/ abbrev GammaZeroCusp (N : ℕ) := MulAction.orbitRel.Quotient (Gamma0 N) (OnePoint ℚ)
/-- The positive divisors used in the squarefree-level cusp classification. -/ abbrev LevelDivisor (N : ℕ) := { d : ℕ // d ∣ N }
/-- The standard representative attached to a divisor `d ∣ N`. -/ def squarefreeCuspPoint (N : ℕ) (d : LevelDivisor N) : OnePoint ℚ := if d.1 = 1 then (0 : ℚ) else if d.1 = N then OnePoint.infty else ((1 / (d.1 : ℚ) : ℚ) : OnePoint ℚ)
/-- The corresponding orbit class on `X₀(N)`. -/ def squarefreeCuspRepresentative (N : ℕ) (d : LevelDivisor N) : GammaZeroCusp N := Quotient.mk'' (squarefreeCuspPoint N d)
/-- General E4/E11 squarefree-level cusp classification. -/ def SquarefreeGammaZeroCuspClassification : Prop := ∀ (N : ℕ), N ≠ 0 → Squarefree N → Function.Bijective (squarefreeCuspRepresentative N)
end SptCM.RolenLiterature
namespace SptCM
end SptCM
namespace SptCM
/-- Possible pairs `(a,b)` with `1 ≤ a ≤ M` and `|b| ≤ a`, encoded by finite types. The second coordinate represents `b+a`. -/ abbrev ReducedFormIndex (M : ℕ) := Σ a : Fin M, Fin (2 * (a.val + 1) + 1)
/-- Decode the positive first coefficient. -/ def ReducedFormIndex.a {M : ℕ} (i : ReducedFormIndex M) : ℕ := i.1.val + 1
/-- Decode the signed middle coefficient. -/ def ReducedFormIndex.b {M : ℕ} (i : ReducedFormIndex M) : ℤ := (i.2.val : ℤ) - (i.a : ℤ)
/-- The usual reduced positive forms of discriminant `-n`, represented by their bounded pair `(a,b)`; the coefficient `c` is uniquely determined by the discriminant equation. -/ def IsReducedFormIndex (n : ℕ) (i : ReducedFormIndex (Nat.sqrt (n / 3))) : Prop :=
  ∃ c : ℕ, i.b ^ 2 - 4 * (i.a : ℤ) * c = -(n : ℤ) ∧ i.a ≤ c ∧ ((Int.natAbs i.b = i.a ∨ i.a = c) → 0 ≤ i.b)
/-- The elementary negative-discriminant class number used here is the number of reduced positive forms. For fundamental negative discriminants this is the standard form-class definition of `h(-n)`. -/ noncomputable def negativeClassNumber (n : ℕ) : ℕ := by classical exact Fintype.card { i : ReducedFormIndex (Nat.sqrt (n / 3)) // IsReducedFormIndex n i }
end SptCM
namespace SptCM
noncomputable section
open Polynomial
open PaperInterfaces
/-- An integral binary quadratic form `[a,b,c]`. -/ structure IntegralBinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ
/-- The raw oriented level-six forms of discriminant `-n`. Passage to `Γ₀(6)`-classes and the finiteness/cardinality theorem are external arithmetic inputs, represented below by finite index types and cardinality hypotheses. -/ def rawOrientedForms (n r : ℕ) : Set IntegralBinaryQuadraticForm :=
  {Q | Q.b ^ 2 - 4 * Q.a * Q.c = -(n : ℤ) ∧ 0 < Q.a ∧ (6 : ℤ) ∣ Q.a ∧ Q.b % 12 = (r : ℤ) % 12 ∧ Nat.gcd (Nat.gcd Q.a.natAbs Q.b.natAbs) Q.c.natAbs = 1}
/-- An integral matrix in `Γ₀(6)`: determinant one and lower-left entry divisible by six. -/ structure GammaZeroSixMatrix where
  p : ℤ
  q : ℤ
  s : ℤ
  t : ℤ
  determinant_one : p * t - q * s = 1
  lowerLeft_dvd : (6 : ℤ) ∣ s
/-- Change of variables of an integral binary quadratic form by a matrix `((p,q),(s,t))`. -/ def transformQuadraticForm (g : GammaZeroSixMatrix) (Q : IntegralBinaryQuadraticForm) : IntegralBinaryQuadraticForm where
  a := Q.a * g.p ^ 2 + Q.b * g.p * g.s + Q.c * g.s ^ 2
  b := 2 * Q.a * g.p * g.q + Q.b * (g.p * g.t + g.q * g.s) + 2 * Q.c * g.s * g.t
  c := Q.a * g.q ^ 2 + Q.b * g.q * g.t + Q.c * g.t ^ 2
/-- A raw oriented form, before quotienting by `Γ₀(6)`. -/ abbrev RawOrientedForm (n r : ℕ) := { Q // Q ∈ rawOrientedForms n r }
/-- The one-step `Γ₀(6)` change-of-variables relation on oriented forms. -/ def gammaZeroSixRelated (n r : ℕ) (Q Q' : RawOrientedForm n r) : Prop := ∃ g : GammaZeroSixMatrix, transformQuadraticForm g Q.1 = Q'.1
/-- The oriented quadratic-form classes `𝒬_{n,r}`: primitive positive definite forms of discriminant `-n`, with `6 ∣ a` and `b ≡ r (mod 12)`, modulo `Γ₀(6)`. `EqvGen` packages the equivalence closure of the concrete change-of-variables relation. -/ def orientedForms (n r : ℕ) : Type :=
  Quotient (Relation.EqvGen.setoid (gammaZeroSixRelated n r))
/-- The level-six eta quotient, parameterized by the analytic eta function. This separates its algebraic formula from the cited modularity and integral model results. -/ def hauptmodul (eta : ℂ → ℂ) (τ : ℂ) : ℂ := eta τ ^ 5 * eta (3 * τ) / (eta (2 * τ) * eta (6 * τ) ^ 5)
section ClassPolynomial
variable {R : Type*} [CommRing R] [Nontrivial R]
/-- The polynomial whose roots are a finite family of CM coordinates. -/ def classPolynomial {ι : Type*} [Fintype ι] (t : ι → R) : R[X] := ∏ i, (X - C (t i))
end ClassPolynomial
end
end SptCM
namespace SptCM.RolenLiterature
/-- A congruence on one explicitly specified arithmetic progression. -/ def SptProgressionCongruence (modulus shift : ℕ) : Prop := ∀ k : ℕ, modulus ∣ spt (modulus * k + shift)
/-- Andrews' modulus-five congruence. -/ def Andrews5 : Prop := SptProgressionCongruence 5 4
/-- Andrews' modulus-seven congruence. -/ def Andrews7 : Prop := SptProgressionCongruence 7 5
/-- Andrews' modulus-thirteen congruence. -/ def Andrews13 : Prop := SptProgressionCongruence 13 6
/-- E1 (Andrews): exactly the three published congruences, with the shifts `4`, `5`, and `6` appearing in the source. Primality and the computation of the canonical inverse of `24` are deliberately not external assumptions. -/ def E1AndrewsCongruences : Prop := Andrews5 ∧ Andrews7 ∧ Andrews13
/-- E2 (Ahlgren--Kim, Theorem 3): the exact finite-range exclusion used at the final cutoff. -/ def E2AhlgrenKimFiniteExclusion : Prop := ∀ ℓ : ℕ, CanonicalCongruencePrime ℓ → ℓ < 10 ^ 11 → ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13
/-- E2 (Ahlgren--Kim, Proposition 6): their normalized theta-cycle input, only in the prime range in which it is cited. -/ def E2AhlgrenKimThetaCycle : Prop := ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → SptCM.Analytic.AhlgrenKimThetaCycleFromUInput ℓ
/-- Neutral operations in the general completion/shadow and Hecke theorem. -/ structure HarmonicMaassModel (Completion Series : Type*) where
  holomorphicPart : Completion → Series
  shadow : Completion → Series
  heckeThreeHalves : ℕ → Completion → Completion
  heckeOneHalf : ℕ → Series → Series
  shadowScale : ℕ → Series → Series
/-- E3 (Bringmann): existence of the completion with the published holomorphic part and normalized eta shadow. -/ def BringmannCompletion {Completion Series : Type*} (M : HarmonicMaassModel Completion Series) (f eta : Series) (shadowNormalization : Series → Series) : Prop :=
  ∃ F : Completion, M.holomorphicPart F = f ∧ M.shadow F = shadowNormalization eta
/-- Neutral output of the general Bruinier--Ono lift. -/ structure BorcherdsLiftModel (Input Product Divisor : Type*) where
  admissibleInput : Input → Prop
  lift : Input → Product
  divisor : Product → Divisor
  predictedDivisor : Input → Divisor
  hasUnitaryCharacter : Product → Prop
  hasProductExpansion : Input → Product → Prop
/-- E5 (Bruinier--Ono, Theorem 6.1): the general lift theorem. It says nothing here about Rolen's particular input or normalized quotient. -/ def E5BruinierOno {Input Product Divisor : Type*} (M : BorcherdsLiftModel Input Product Divisor) : Prop :=
  ∀ F, M.admissibleInput F → M.divisor (M.lift F) = M.predictedDivisor F ∧ M.hasUnitaryCharacter (M.lift F) ∧ M.hasProductExpansion F (M.lift F)
/-- Neutral data in the general Weyl-vector formula. -/ structure WeylVectorModel (Input Theta Scalar Cusp : Type*) where
  admissibleInput : Input → Prop
  weylVector : Input → Cusp → Scalar
  regularizedPairing : Input → Theta → Scalar
  cuspTheta : Cusp → Theta
  normalization : Scalar → Scalar
/-- E6 (Bruinier--Schwagenscheidt, equation (11)): the Weyl vector at each cusp is the normalized regularized theta pairing. -/ def E6BruinierSchwagenscheidt {Input Theta Scalar Cusp : Type*} (M : WeylVectorModel Input Theta Scalar Cusp) : Prop :=
  ∀ F c, M.admissibleInput F → M.weylVector F c = M.normalization (M.regularizedPairing F (M.cuspTheta c))
/-- General eta-quotient and integral modular-curve predicates used in E7. -/ structure LigozatModel (Exponent Quotient Cusp Order Curve : Type*) where
  ligozatConditions : Exponent → Prop
  quotient : Exponent → Quotient
  isModularFunction : Quotient → Prop
  cuspOrder : Quotient → Cusp → Order
  orderFormula : Exponent → Cusp → Order
  characterCriterion : Exponent → Prop
  hasTrivialCharacter : Quotient → Prop
  isLevelSixModularCurve : Curve → Prop
  isIntegralModelAwayFromLevel : Curve → Prop
  hasGenusZeroGeometricFibers : Curve → Prop
  hasDisjointStandardCuspSections : Curve → Prop
/-- E7: Ligozat's general modularity, character, and cusp-order theorem. -/ def LigozatEtaQuotients {Exponent Quotient Cusp Order Curve : Type*} (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop :=
  ∀ e, M.ligozatConditions e → M.isModularFunction (M.quotient e) ∧ (∀ c, M.cuspOrder (M.quotient e) c = M.orderFormula e c) ∧ (M.characterCriterion e → M.hasTrivialCharacter (M.quotient e))
/-- E7: good integral model of the compactified level-six modular curve away from the level. -/ def X0SixGoodIntegralModel {Exponent Quotient Cusp Order Curve : Type*} (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop := ∀ X : Curve, M.isLevelSixModularCurve X → M.isIntegralModelAwayFromLevel X
/-- E7: smooth irreducible genus-zero geometric fibers away from six. -/ def X0SixGenusZeroFibers {Exponent Quotient Cusp Order Curve : Type*} (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop := ∀ X : Curve, M.isLevelSixModularCurve X → M.hasGenusZeroGeometricFibers X
/-- E7: disjointness of the four standard cusp sections away from six. -/ def X0SixDisjointCusps {Exponent Quotient Cusp Order Curve : Type*} (M : LigozatModel Exponent Quotient Cusp Order Curve) : Prop := ∀ X : Curve, M.isLevelSixModularCurve X → M.hasDisjointStandardCuspSections X
/-- Operations on rational functions on a proper integral curve. This is a neutral geometric model: it contains no eta quotient, CM point, Hauptmodul, or paper-specific conclusion. -/ structure IntegralCurveFunctionGeometry (Function Divisor Curve Section Expansion : Type*) where
  divisor : Function → Divisor
  sectionDifference : Curve → Section → Section → Divisor
  hasNoInteriorZeroOrPole : Function → Curve → Prop
  hasIntegralUnitExpansionAt : Function → Section → Expansion → Prop
  hasNoVerticalComponent : Function → Curve → Prop
  identifiesWithProjectiveLine : Function → Curve → Prop
/-- General horizontal-divisor principle: on a smooth proper curve, a rational function with no interior zero or pole and cusp orders `+1,-1` has divisor the difference of those two cusp sections. -/ def E7HorizontalDivisorPrinciple {Function Divisor Curve Section Expansion Order : Type*} [Zero Order] [One Order] [Neg Order] (G : IntegralCurveFunctionGeometry Function Divisor Curve Section Expansion) (isIntegralModel hasGenusZeroFibers : Curve → Prop) (isRationalFunction : Function → Prop)
    (cuspOrder : Function → Section → Order) : Prop := ∀ X f zero infinity, isIntegralModel X → hasGenusZeroFibers X → isRationalFunction f → G.hasNoInteriorZeroOrPole f X → cuspOrder f zero = 1 → cuspOrder f infinity = -1 → (∀ c, c ≠ zero → c ≠ infinity → cuspOrder f c = 0) → G.divisor f = G.sectionDifference X zero infinity
/-- General integral spreading principle: an integral unit expansion at a horizontal cusp excludes an additional vertical divisor component. -/ def E7NoVerticalComponentPrinciple {Function Divisor Curve Section Expansion : Type*} (G : IntegralCurveFunctionGeometry Function Divisor Curve Section Expansion) (isIntegralModel hasDisjointStandardCuspSections : Curve → Prop) : Prop :=
  ∀ X f zero infinity expansion, isIntegralModel X → hasDisjointStandardCuspSections X → G.divisor f = G.sectionDifference X zero infinity → G.hasIntegralUnitExpansionAt f infinity expansion → G.hasNoVerticalComponent f X
/-- General degree-one divisor criterion on a smooth proper integral genus-zero model. -/ def E7IntegralDegreeOneCriterion {Function Divisor Curve Section Expansion : Type*} (G : IntegralCurveFunctionGeometry Function Divisor Curve Section Expansion) (isIntegralModel hasGenusZeroFibers hasDisjointStandardCuspSections : Curve → Prop) : Prop :=
  ∀ X f zero infinity, isIntegralModel X → hasGenusZeroFibers X → hasDisjointStandardCuspSections X → G.divisor f = G.sectionDifference X zero infinity → G.hasNoVerticalComponent f X → G.identifiesWithProjectiveLine f X
/-- The concrete finite type counted by `negativeClassNumber`. -/ abbrev ReducedFormClasses (n : ℕ) := { i : ReducedFormIndex (Nat.sqrt (n / 3)) // IsReducedFormIndex n i }
/-- In the odd negative-discriminant case used here, `-n` is fundamental exactly when `n` is squarefree and `n ≡ 3 (mod 4)`. -/ def IsNegativeFundamentalDiscriminant (n : ℕ) : Prop := Squarefree n ∧ n % 4 = 3
/-- The canonical quadratic order `ℤ[(1 + √(-n))/2] = ℤ[X]/(X²-X+(n+1)/4)` in the paper's range `n ≡ 3 (mod 4)`. Using this concrete quotient prevents substitution of an unrelated domain with a conveniently chosen class number. -/ abbrev NegativeQuadraticOrder (n : ℕ) :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
/-- Additional unproved E8 input: the specified negative quadratic order is a domain in the fundamental-discriminant range. No theorem-level source for the exact interface is certified. -/ def E8NegativeQuadraticOrderDomain (n : ℕ) : Prop :=
  IsNegativeFundamentalDiscriminant n → Nonempty (IsDomain (NegativeQuadraticOrder n))
/-- Additional unproved E8 input: reduced forms correspond to proper ideal classes with these boundary conventions. This exact correspondence has not been proved or matched to a cited theorem. -/ def E8ReducedFormClassification (n : ℕ) [IsDomain (NegativeQuadraticOrder n)] : Prop :=
  IsNegativeFundamentalDiscriminant n → Nonempty (ClassGroup (NegativeQuadraticOrder n) ≃ ReducedFormClasses n)
/-- The standard fixed-local-orientation refinement of the form/ideal-class correspondence. Choosing one prime above each of `2` and `3` gives four possibilities, represented by the residues `1, 11, 5, 7` modulo `12`. This datum contains neither an action nor a cardinality equation. -/ structure FourOrientedClassEquivalences (n : ℕ) [IsDomain (NegativeQuadraticOrder n)] where
  orientation1 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 1
  orientation11 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 11
  orientation5 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 5
  orientation7 : ClassGroup (NegativeQuadraticOrder n) ≃ orientedForms n 7
/-- Additional unproved E8 input: the four concrete level-six oriented-form quotients are the four specified proper ideal-class torsors. Their exact equivalences require separate justification. -/ def E8FourOrientedFormClassification (n : ℕ) [IsDomain (NegativeQuadraticOrder n)] : Prop :=
  IsNegativeFundamentalDiscriminant n → n % 24 = 23 → Nonempty (FourOrientedClassEquivalences n)
/-- Neutral CM/class-field/reduction data. -/ structure CMTheoryModel (Order IdealClass CMPoint Reduction Endomorphism : Type*) where
  acts : IdealClass → CMPoint → CMPoint
  classCount : Order → ℕ
  pointsForOrder : Order → Set CMPoint
  actionSimplyTransitive : Order → Prop
  classCountCorrect : Order → Prop
  hasPotentiallyGoodReduction : CMPoint → Prop
  reduction : CMPoint → Reduction
  inertAt : ℕ → CMPoint → Prop
  supersingular : Reduction → Prop
  specializedAction : CMPoint → Endomorphism
  specializationInjective : CMPoint → Prop
/-- Additional unproved E8 application interface: the specified quadratic-order families specialize compatibly with conjugation and the level-six structure. No collision, noncommutation, volume or separation conclusion is assumed here. -/ structure E8OrientedQuadraticSpecialization (n : ℕ) {Order IdealClass CMPoint Reduction D : Type*} [DivisionRing D] [Star D] (M : CMTheoryModel Order IdealClass CMPoint Reduction D) where
  point : ∀ r : ℕ, RawOrientedForm n r → CMPoint
  specialize : ∀ {r : ℕ}, RawOrientedForm n r → NegativeQuadraticOrder n →+* D
  specializedGenerator : ∀ {r : ℕ} (Q : RawOrientedForm n r), M.specializedAction (point r Q) = specialize Q (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))
  conjugationGenerator : ∀ {r : ℕ} (Q : RawOrientedForm n r), star (specialize Q (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))) = 1 - specialize Q (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)))
  levelOrder : Subring D
  levelAction : levelOrder →+* ZMod 6
  specializedGenerator_mem_levelOrder : ∀ {r : ℕ} (Q : RawOrientedForm n r), M.specializedAction (point r Q) ∈ levelOrder
  levelAction_specializedGenerator : ∀ {r : ℕ} (Q : RawOrientedForm n r), levelAction ⟨M.specializedAction (point r Q), specializedGenerator_mem_levelOrder Q⟩ = (((r + 1) / 2 : ℕ) : ZMod 6)
/-- Additional unproved E8 application datum: the actual analytic CM values have the specified finite Galois realization and permutation actions. No coefficients of root polynomials are asserted here. -/ structure E8FiniteGaloisCMReciprocity (I J L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] (x : I → ℂ) (y : J → ℂ) where
  embedding : L →ₐ[ℚ] ℂ
  embedding_injective : Function.Injective embedding
  algebraicX : I → L
  algebraicY : J → L
  realizesX : ∀ i, embedding (algebraicX i) = x i
  realizesY : ∀ j, embedding (algebraicY j) = y j
  permutationX : ∀ _σ : L ≃ₐ[ℚ] L, I ≃ I
  permutationY : ∀ _σ : L ≃ₐ[ℚ] L, J ≃ J
  reciprocityX : ∀ (σ : L ≃ₐ[ℚ] L) i, σ (algebraicX i) = algebraicX (permutationX σ i)
  reciprocityY : ∀ (σ : L ≃ₐ[ℚ] L) j, σ (algebraicY j) = algebraicY (permutationY σ j)
/-- Additional unproved E8 integral refinement: each specified CM root is integral over the chosen coefficient ring. This exact realization is assumed, not derived from a certified literature theorem. -/ structure E8FiniteGaloisIntegralCMReciprocity (A I J L : Type*) [CommRing A] [Field L] [Algebra A L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] (x : I → ℂ) (y : J → ℂ) extends E8FiniteGaloisCMReciprocity I J L x y where
  integralX : ∀ i, IsIntegral A (toE8FiniteGaloisCMReciprocity.algebraicX i)
  integralY : ∀ j, IsIntegral A (toE8FiniteGaloisCMReciprocity.algebraicY j)
/-- Additional unproved E8 application premise: good reduction in the specified CM model. -/ def CMPotentialGoodReduction {Order IdealClass CMPoint Reduction Endomorphism : Type*} (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop := ∀ P, M.hasPotentiallyGoodReduction P
/-- Additional unproved E8 application premise motivated by Deuring reduction theory. Its exact match to this model is not certified. -/ def DeuringInertSupersingular {Order IdealClass CMPoint Reduction Endomorphism : Type*} (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop := ∀ ℓ P, M.inertAt ℓ P → M.supersingular (M.reduction P)
/-- Additional unproved E8 application premise: injectivity of the relevant CM-order action after specialization. -/ def CMSpecializationInjective {Order IdealClass CMPoint Reduction Endomorphism : Type*} (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop := ∀ P, M.specializationInjective P
/-- Compatibility conjunction for the reduction branch. -/ def E8StandardCMReduction {Order IdealClass CMPoint Reduction Endomorphism : Type*} (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop := CMPotentialGoodReduction M ∧ DeuringInertSupersingular M ∧ CMSpecializationInjective M
/-- Compatibility interface used by the existing reduction branch. Its first conjunct is intentionally *not* used for I22; the pinned declarations `E8ReducedFormClassification` and `E8IdealClassAction` above replace it there. -/ def E8StandardCM {Order IdealClass CMPoint Reduction Endomorphism : Type*} (M : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) : Prop :=
  (∀ O, M.actionSimplyTransitive O ∧ M.classCountCorrect O) ∧ E8StandardCMReduction M
/-- Neutral level-order and covolume data for E9. -/ structure EichlerCovolumeModel (Curve Subgroup Order Lattice Vector : Type*) where
  supersingular : Curve → Prop
  cyclicOfOrderSix : Subgroup → Prop
  preservingOrder : Curve → Subgroup → Order
  isEichlerOfLevelSix : Order → Prop
  independent : Vector → Vector → Vector → Vector → Prop
  span : Vector → Vector → Vector → Vector → Lattice
  covolume : Lattice → ℝ
  squaredNorm : Vector → ℝ
/-- E9 (Arpin): the level-six Eichler-order theorem. -/ def ArpinLevelSix {Curve Subgroup Order Lattice Vector : Type*} (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop := ∀ E C, M.supersingular E → M.cyclicOfOrderSix C → M.isEichlerOfLevelSix (M.preservingOrder E C)
/-- E9 (Goren--Lauter): the general four-vector covolume/Hadamard bound. -/ def GorenLauterHadamard {Curve Subgroup Order Lattice Vector : Type*} (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop :=
  ∀ a b c d, M.independent a b c d → M.covolume (M.span a b c d) ^ 2 ≤ M.squaredNorm a * M.squaredNorm b * M.squaredNorm c * M.squaredNorm d
/-- Compatibility conjunction for older callers. -/ def E9ArpinGorenLauter {Curve Subgroup Order Lattice Vector : Type*} (M : EichlerCovolumeModel Curve Subgroup Order Lattice Vector) : Prop := ArpinLevelSix M ∧ GorenLauterHadamard M
/-- Constancy of a genuine Dirichlet character on `H` consecutive integers. `DirichletCharacter` supplies multiplicativity, periodicity and the extension by zero at non-units; these were missing from the old arbitrary-function formulation. -/ def ConstantDirichletOnInterval {R : Type*} [CommMonoidWithZero R] {ℓ : ℕ} (χ : DirichletCharacter R ℓ) (a : ℤ) (H : ℕ) : Prop :=
  ∀ i j : ℕ, i < H → j < H → χ (a + (i : ℤ)) = χ (a + (j : ℤ))
/-- E10 (Treviño, corrected): the all-prime constant-character estimate with constant `3.38`. Nonprincipality is the standard condition `χ ≠ 1`, not a caller-chosen predicate. -/ def E10TrevinoCorrected : Prop :=
  ∀ (ℓ H : ℕ) (χ : DirichletCharacter ℂ ℓ) (a : ℤ), ℓ.Prime → χ ≠ 1 → ConstantDirichletOnInterval χ a H → (H : ℝ) ≤ 3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ
/-- The operations occurring in the general finite-height Stokes theorem. An input comprises a qualified weakly holomorphic form together with a harmonic-Maass completion. The remaining fields are the actual numerical quantities in the truncated identity; in particular, the conclusion is not hidden behind an application-chosen predicate. -/ structure FiniteHeightStokesModel (Input : Type*) where
  qualified : Input → Prop
  shadowScale : Input → ℝ
  truncatedIntegral : Input → ℕ → ℝ
  holomorphicConstantTerm : Input → ℝ
  topBoundaryError : Input → ℕ → ℝ
  regularizedPairing : Input → ℝ
/-- The exact output of finite-height Stokes: the truncated-domain identity, convergence to the regularized pairing, and decay of the nonholomorphic top boundary. -/ def FiniteHeightStokesConclusion {Input : Type*} (M : FiniteHeightStokesModel Input) (x : Input) : Prop :=
  (∀ T, M.shadowScale x * M.truncatedIntegral x T = M.holomorphicConstantTerm x + M.topBoundaryError x T) ∧ Filter.Tendsto (M.truncatedIntegral x) Filter.atTop (nhds (M.regularizedPairing x)) ∧ Filter.Tendsto (M.topBoundaryError x) Filter.atTop (nhds 0)
/-- E11: the general finite-height Stokes theorem, with its full numerical identity and both limiting assertions exposed. -/ def FiniteHeightStokesTheorem {Input : Type*} (M : FiniteHeightStokesModel Input) : Prop := ∀ x, M.qualified x → FiniteHeightStokesConclusion M x
end SptCM.RolenLiterature
namespace SptCM.Analytic.Repaired
open SptCM.RolenLiterature
open SptCM.Analytic
/-- The characteristic-free prime range used by the initial `f`-identity. -/ def ValidLevelPrime (p : ℕ) : Prop := p.Prime ∧ Nat.Coprime p 6
/-- Re-export of the cycle-free, exact literature interface. This is an abbreviation, not a second grid theorem or a new caller-chosen family. -/ abbrev AhlgrenKimGridTheorem (K : Type*) [Field K] := SptCM.RolenLiterature.AhlgrenKimGridTheorem K
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
/-- The actual left side of the `f`-Hecke identity in the coefficient model. -/ def fHeckeDifference {K : Type*} [Field K] (p : ℕ) (chiP : K) (legendre : ℤ → K) (f : QSeries K) : QSeries K := fun r => heckeThreeHalf p chiP legendre f r - chiP * (1 + (p : K)) * f r
/-- Mathlib's Legendre symbol, cast to the coefficient field used by the Hecke coefficient formula. -/ def heckeLegendreCast {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (r : ℤ) : K := (legendreSym p r : ℤ)
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
/-- The conventionally zero term `G_{m/p}` when `p ∤ m`. When `m=p`, this is `G₁`, so the published convention `G₁=0` gives the required cancellation. -/ def gridDivisorTerm {K : Type*} [Zero K] (G : ℕ → QSeries K) (m p : ℕ) : QSeries K := if p ∣ m then G (m / p) else 0
/-- The source-normalized left side of Rolen's grid Hecke recurrence, solved for `G_{mp}`. -/ def normalizedGridHeckeLeft {K : Type*} [Field K] (p m : ℕ) (chi : ℕ → K) (legendre : ℤ → K) (G : ℕ → QSeries K) : QSeries K := fun r => (p : K)⁻¹ * (heckeThreeHalf p (chi p) legendre (G m) r - chi p * legendre ((m : ℤ) ^ 2) * G m r - gridDivisorTerm G m p r + (p : K) * chi m * G p r)
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
open SptCM.RolenLiterature
/-- The actual Legendre symbol made total in the index `p`; all I05 uses specialize it at a prime. -/ def actualHeckeLegendre {K : Type*} [Field K] (p : ℕ) (r : ℤ) : K :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    heckeLegendreCast p r
  else 0
/-- The actual normalized left side of the `f`-Hecke identity. -/ def actualFHeckeLeft {K : Type*} [Field K] [CharZero K] (G : PublishedMockModularGrid K) (p : ℕ) : QSeries K := fun r => (p : K)⁻¹ * fHeckeDifference p (G.chi p) (actualHeckeLegendre p) (fun s => (fSeries s : K)) r
/-- The actual normalized left side of the grid Hecke recurrence. -/ def actualGridHeckeLeft {K : Type*} [Field K] (G : PublishedMockModularGrid K) (m p : ℕ) : QSeries K := normalizedGridHeckeLeft p m G.chi (actualHeckeLegendre p) G.grid
/-- Exact E3/E4 application boundary used in I05. These are only the modular/shadow qualifications supplied by the cited analytic theory; neither a principal-part assertion nor either desired Hecke identity is a field. -/ structure SourceI05Qualification {K : Type*} [Field K] [CharZero K] (G : PublishedMockModularGrid K) : Prop where
  f_left_qualifies : ∀ p, ValidLevelPrime p → G.Qualifies p (actualFHeckeLeft G p)
  grid_left_qualifies : ∀ m p, 1 < m → Nat.Coprime m 6 → ValidLevelPrime p → G.Qualifies (m * p) (actualGridHeckeLeft G m p)
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic SptCM.RolenLiterature
/-- The one integral published grid, together with its characteristic-zero realization. Integrality of the grid coefficients is part of the cited grid theorem; the Hecke identities are not fields. -/ structure IntegralGridRealization where
  grid : ℕ → QSeries ℤ
  rationalGrid : PublishedMockModularGrid ℚ
  rational_grid : ∀ m r, rationalGrid.grid m r = (grid m r : ℚ)
  sourceQualification : SourceI05Qualification rationalGrid
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
/-- The four nonzero values of the primitive quadratic character modulo twelve, written on the canonical representatives. -/ def chiTwelveResidue (s : Fin 12) : ℤ := if s = 1 then 1 else if s = 5 then -1 else if s = 7 then -1 else if s = 11 then 1 else 0
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- The inverse primitive twelfth root used by the Fourier transform `e(-rs/12)`. -/ noncomputable def inverseTwelfthRoot : ℂ := (Real.sqrt 3 / 2 : ℂ) - Complex.I / 2
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open scoped BigOperators
/-- The component vector `c (e₁ - e₅ - e₇ + e₁₁)`, evaluated on the canonical representatives of `ℤ / 12ℤ`. -/ def fourComponentVector (c : ℂ) (r : Fin 12) : ℂ := c * (chiTwelveResidue r : ℂ)
/-- The normalized finite Fourier matrix giving the level-twelve Weil `S`-generator, with the same inverse-root convention as the Gauss sum. -/ noncomputable def levelTwelveWeilS (x : Fin 12 → ℂ) (s : Fin 12) : ℂ := (Real.sqrt 12 : ℂ)⁻¹ * ∑ r : Fin 12, inverseTwelfthRoot ^ ((r.val * s.val) % 12) * x r
/-- The common `T` multiplier of the four supported components. -/ noncomputable def levelTwelveTMultiplier : ℂ := Complex.exp (Complex.I * (Real.pi / 12 : ℂ))
/-- The diagonal level-twelve Weil `T`-generator. The exponent is the quadratic residue `r² mod 24`; all four supported indices have residue one. -/ noncomputable def levelTwelveWeilT (x : Fin 12 → ℂ) (r : Fin 12) : ℂ := levelTwelveTMultiplier ^ ((r.val ^ 2) % 24) * x r
/-- Exact E4 generator data for eta times an integral polynomial in `j`. The two displayed equalities are the standard scalar `S`- and `T`-laws; they are required for every polynomial, rather than merely recorded as an opaque qualification predicate. -/ structure EtaJGeneratorBasis (Form : Type*) [SMul ℂ Form] extends EtaJPowerBasis Form where
  slashS : Form → Form
  slashT : Form → Form
  polynomial_slashS : ∀ P : Polynomial ℤ, slashS (polynomialForm P) = polynomialForm P
  polynomial_slashT : ∀ P : Polynomial ℤ, slashT (polynomialForm P) = levelTwelveTMultiplier • polynomialForm P
/-- The actual separated vector-valued input: its scalar form and its integral Fourier series are fixed simultaneously. Its finite component vector is the canonical `e₁-e₅-e₇+e₁₁`, not caller-supplied data. -/ structure FourComponentInput (Form : Type*) where
  scalarForm : Form
  scalarSeries : HForm ℤ
/-- The concrete I10 input obtained from the triangular eta--j construction. -/ noncomputable def auxiliaryFourComponentInput {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (k : ℕ) (a : ℤ) : FourComponentInput Form
    where
  scalarForm := auxiliaryForm E.toEtaJPowerBasis k a
  scalarSeries := auxiliaryHn E.toEtaJPowerBasis k a
/-- The combined scalar/finite `S` equation. The left side applies the analytic slash action to the scalar form; the right side applies the exact level-twelve Weil matrix to its fixed finite component. -/ def HasFourComponentWeilS {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  (E.slashS F.scalarForm, fourComponentVector 1) = (F.scalarForm, levelTwelveWeilS (fourComponentVector 1))
/-- The combined scalar/finite `T` equation, with the common multiplier `e(1/24)` shown on the opposite tensor factor on the two sides. -/ def HasFourComponentWeilT {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  (E.slashT F.scalarForm, fun r => levelTwelveTMultiplier * fourComponentVector 1 r) = (levelTwelveTMultiplier • F.scalarForm, levelTwelveWeilT (fourComponentVector 1))
/-- Exact level-twelve Weil-generator law for a separated four-component input. Both equalities simultaneously contain the scalar eta--j law and the finite matrix calculation. -/ def HasFourComponentWeilGeneratorLaw {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (F : FourComponentInput Form) : Prop :=
  HasFourComponentWeilS E F ∧ HasFourComponentWeilT E F
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
/-- The four divisors indexing the cusps of squarefree level six. -/ def IsLevelSixDivisor (c : ℕ) : Prop := c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 6
/-- Multiplier description of the simultaneous congruences `σ_c(r) ≡ -r (mod 2c)` and `σ_c(r) ≡ r (mod 12/c)` at level six. -/ def atkinLehnerMultiplier (c : ℕ) : ℕ := if c = 1 then 1 else if c = 2 then 7 else if c = 3 then 5 else 11
/-- The Atkin--Lehner permutation `σ_c` on `ℤ/12ℤ`. -/ def atkinLehnerSigma (c : ℕ) (r : Fin 12) : Fin 12 := ⟨(atkinLehnerMultiplier c * r.val) % 12, Nat.mod_lt _ (by norm_num)⟩
/-- The signed component theta series appearing in Euler's eta identity. -/ def signedComponentThetaSeries {V : Type*} [AddCommMonoid V] [Module ℂ V] (theta : Fin 12 → V) : V := ∑ r, (chiTwelveResidue r : ℂ) • theta r
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- Exact general Euler theta identity in a complex series model. This is the standard scalar identity, not a cusp contraction or Weyl-vector assertion. -/ def EtaComponentThetaIdentity {V : Type*} [AddCommMonoid V] [Module ℂ V] (theta : Fin 12 → V) (eta : V) : Prop := signedComponentThetaSeries theta = (2 : ℂ) • eta
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
open SptCM.RolenLiterature
open scoped BigOperators
/-- The genuinely coefficient-theoretic constant term of `H f`, written as a finite convolution once `H` has no terms below `-n` and `f` has no negative terms below `-1`. -/ noncomputable def finiteMockProductConstantTerm (n : ℕ) (H : HForm ℤ) : ℤ := ∑ r ∈ Finset.Icc (-(n : ℤ)) 1, H r * aCoeff (-r)
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- The numerical shadow factor in the paper's Stokes formula. -/ noncomputable def publishedShadowScale : ℝ := 3 * Real.sqrt 6 / Real.pi
/-- A Stokes input remembers the coefficient series to which the completion is paired. It contains no boundary identity, limit, or pairing conclusion. -/ structure HnStokesInput (Completion : Type*) where
  index : ℕ
  coefficients : HForm ℤ
  completion : Completion
/-- The concrete finite-height Stokes model used in the paper. Its scale and holomorphic boundary term are fixed definitions: only the genuinely analytic qualification, truncated integrals, errors, and regularized values are parameters. -/ noncomputable def hnFiniteHeightStokesModel {Completion : Type*} (qualified : HnStokesInput Completion → Prop) (truncatedIntegral topBoundaryError : HnStokesInput Completion → ℕ → ℝ) (regularizedValue : HnStokesInput Completion → ℝ) : FiniteHeightStokesModel (HnStokesInput Completion)
    where
  qualified := qualified
  shadowScale := fun _ => publishedShadowScale
  truncatedIntegral := truncatedIntegral
  holomorphicConstantTerm := fun x => (finiteMockProductConstantTerm x.index x.coefficients : ℝ)
  topBoundaryError := topBoundaryError
  regularizedPairing := regularizedValue
/-- The actual pair consisting of the triangularly constructed `H_n` and a chosen Bringmann completion. -/ noncomputable def actualHnStokesInput {Form Completion : Type*} (E : EtaJPowerBasis Form) (k : ℕ) (F : Completion) : HnStokesInput Completion
    where
  index := 24 * k - 1
  coefficients := auxiliaryHn E k (aCoeff ((24 * k - 1 : ℕ) : ℤ))
  completion := F
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.RolenLiterature
/-- The Weyl-vector model in which the regularized pairing is the signed sum of the twelve component pairings and the cusp theta function is obtained by the explicit Atkin--Lehner permutation. -/ def componentWeylVectorModel {Input V : Type*} [AddCommMonoid V] [Module ℂ V] (admissible : Input → Prop) (weylVector : Input → ℕ → ℂ) (pairing : Input → V →ₗ[ℂ] ℂ) (theta : Fin 12 → V) (normalization : ℂ → ℂ) : WeylVectorModel Input (Fin 12 → V) ℂ ℕ
    where
  admissibleInput := admissible
  weylVector := weylVector
  regularizedPairing := fun F componentTheta => ∑ r, (chiTwelveResidue r : ℂ) * pairing F (componentTheta r)
  cuspTheta := fun c r => theta (atkinLehnerSigma c r)
  normalization := normalization
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
open scoped BigOperators
/-- A general E4 multiplication/residue interface for the eta--j space and Ahlgren--Kim's grid space. `coefficient_zero` is the ordinary Cauchy product formula for two Laurent expansions once lower bounds are supplied. -/ structure WeightTwoMultiplicationTheory (K Form Product : Type*) [Field K] [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (G : AhlgrenKimGridTheorem K) where
  product : Form → QSeries K → Product
  coefficients : Product → HForm K
  IsWeaklyHolomorphic : Product → Prop
  IsWeightTwo : Product → Prop
  constantTerm : Product → K
  constantTerm_eq_coefficient_zero : ∀ F, constantTerm F = coefficients F 0
  product_is_weaklyHolomorphic : ∀ A m B, E.qualifies A → G.Qualifies m B → IsWeaklyHolomorphic (product A B)
  product_is_weightTwo : ∀ A m B, E.qualifies A → G.Qualifies m B → IsWeightTwo (product A B)
  coefficient_zero : ∀ A B lo hi, (∀ r, r < lo → E.coefficients A r = 0) → (∀ r, r < -hi → B r = 0) → coefficients (product A B) 0 = ∑ r ∈ Finset.Icc lo hi, (E.coefficients A r : K) * B (-r)
  residueTheorem : ∀ F, IsWeaklyHolomorphic F → IsWeightTwo F → constantTerm F = 0
end SptCM.Analytic.Repaired
namespace SptCM.Repair
/-- The signed integer exponent occurring in the Borcherds product. -/ def signedEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℤ := SptCM.Analytic.chi12 (m : ℤ) * H ((m : ℤ) ^ 2)
/-- Positive part of the signed Euler exponent. -/ def positiveEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℕ := (signedEulerExponent H m).toNat
/-- Negative part of the signed Euler exponent. -/ def negativeEulerExponent (H : ℤ → ℤ) (m : ℕ) : ℕ := (-signedEulerExponent H m).toNat
end SptCM.Repair
namespace SptCM.Repair
open scoped PowerSeries
/-- The finite truncation of an Euler product with the indicated factor indices and natural exponents. -/ noncomputable def eulerProductTruncation {R : Type*} [CommRing R] (index exponent : ℕ → ℕ) (N : ℕ) : PowerSeries R := ∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ index i) ^ exponent i
/-- The canonical coefficientwise Euler product: its coefficient in degree `d` is read from the finite truncation through `d + 1`. -/ noncomputable def stabilizedEulerProduct {R : Type*} [CommRing R] (index exponent : ℕ → ℕ) : PowerSeries R :=
  PowerSeries.mk fun d => PowerSeries.coeff d (eulerProductTruncation (R := R) index exponent (d + 2))
/-- The actual numerator Euler product attached to the signed coefficients of `H`. -/ noncomputable def eulerProductPlus {R : Type*} [CommRing R] (H : ℤ → ℤ) : PowerSeries R := stabilizedEulerProduct (R := R) id (positiveEulerExponent H)
/-- The actual denominator Euler product attached to the signed coefficients of `H`. -/ noncomputable def eulerProductMinus {R : Type*} [CommRing R] (H : ℤ → ℤ) : PowerSeries R := stabilizedEulerProduct (R := R) id (negativeEulerExponent H)
end SptCM.Repair
namespace SptCM.Analytic.Repaired
open SptCM.Analytic
/-- The integral twelve-component coefficient function `H v`, where `v = e₁ - e₅ - e₇ + e₁₁`. -/ def fourComponentHSeries (H : HForm ℤ) : ℤ → Fin 12 → ℤ := fun r s => H r * chiTwelveResidue s
/-- Exact coefficient content needed from the four-component input: zero constant coefficient, and a single integral negative index `-n` whose vector is `e₁-e₅-e₇+e₁₁`. -/ def HasFourComponentFourierData (n : ℕ) (V : ℤ → Fin 12 → ℤ) : Prop :=
  (∀ s, V 0 s = 0) ∧ ∀ r : ℤ, r < 0 → ∀ s, V r s = if r = -(n : ℤ) then chiTwelveResidue s else 0
/-- Integral vector Fourier series attached to an actual four-component input. The finite sign vector is fixed by the type of input. -/ def FourComponentInput.vectorSeries {Form : Type*} (F : FourComponentInput Form) : ℤ → Fin 12 → ℤ := fourComponentHSeries F.scalarSeries
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.RolenLiterature
open Polynomial
/-- The exact, concrete specification of the four-component input. Its first conjunct is the combined scalar/finite Weil-generator law, while its second conjunct expands to the zero constant term and the complete integral principal part. There is no caller-chosen predicate or application record. -/ def VectorInputSpec {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) (n : ℕ) (F : FourComponentInput Form) : Prop :=
  HasFourComponentWeilGeneratorLaw E F ∧ HasFourComponentFourierData n F.vectorSeries
end SptCM.Analytic.Repaired
namespace SptCM
noncomputable section
open Polynomial
/-- The coefficient ring `ℤ[1/6]` used by the oriented class polynomials. -/ abbrev AwaySix := Localization.Away (6 : ℤ)
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- Reduction of coefficients in `ℤ[1/6]` to a field of characteristic `ℓ`. The explicit unit hypothesis is precisely the good-prime condition needed by the universal property of localization. -/ def awaySixReduction (ℓ : ℕ) (h6 : IsUnit (6 : ZMod ℓ)) : AwaySix →+* ZMod ℓ :=
  Localization.awayLift (Int.castRingHom (ZMod ℓ)) 6 (by simpa using h6)
end
end SptCM
namespace SptCM
noncomputable section
open Polynomial
/-- The canonical embedding of `ℤ[1/6]` into the complex numbers. -/ def awaySixToComplex : AwaySix →+* ℂ :=
  Localization.awayLift (Int.castRingHom ℂ) 6
    (by
      apply isUnit_iff_ne_zero.mpr
      norm_num)
/-- A finite enumeration of the actual `Γ₀(6)`-oriented quadratic-form classes of discriminant `-n` and orientation `r`. -/ structure OrientedCMEnumeration (n r h : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  classes : Index ≃ orientedForms n r
  card_eq : Fintype.card Index = h
attribute [instance] OrientedCMEnumeration.indexFintype
end
end SptCM
namespace SptCM.CM.Repaired
open SptCM.RolenLiterature
/-- Rolen's analytic Hauptmodul using Mathlib's actual Dedekind eta function, rather than an arbitrary function named `eta`. -/ noncomputable def analyticHauptmodul (τ : UpperHalfPlane) : ℂ := SptCM.hauptmodul ModularForm.eta τ
/-- An eta-exponent vector at the four divisors of level six. -/ structure LevelSixEtaExponents where
  atOne : ℤ
  atTwo : ℤ
  atThree : ℤ
  atSix : ℤ
/-- The exponent vector of Rolen's Hauptmodul. -/ def hauptmodulExponents : LevelSixEtaExponents := ⟨5, -1, 1, -5⟩
/-- Ligozat's order formula at the cusp represented by denominator `c ∣ 6`. The four summands are indexed by `δ = 1,2,3,6`. -/ def ligozatCuspOrder (e : LevelSixEtaExponents) (c : ℕ) : ℚ :=
  (6 : ℚ) / 24 * (((Nat.gcd c 1 : ℚ) ^ 2 * e.atOne) / (Nat.gcd c (6 / c) * c * 1 : ℕ) + ((Nat.gcd c 2 : ℚ) ^ 2 * e.atTwo) / (Nat.gcd c (6 / c) * c * 2 : ℕ) + ((Nat.gcd c 3 : ℚ) ^ 2 * e.atThree) / (Nat.gcd c (6 / c) * c * 3 : ℕ) + ((Nat.gcd c 6 : ℚ) ^ 2 * e.atSix) / (Nat.gcd c (6 / c) * c * 6 : ℕ))
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- The canonical complex CM point attached to a raw oriented quadratic form. -/ def rawCMPoint {n r : ℕ} (Q : RawOrientedForm n r) : ℂ := ((-(Q.1.b : ℂ)) + Complex.I * Real.sqrt n) / (2 * (Q.1.a : ℂ))
theorem rawCMPoint_im {n r : ℕ} (Q : RawOrientedForm n r) : (rawCMPoint Q).im = Real.sqrt n / (2 * Q.1.a) := by
  have haZ : Q.1.a ≠ 0 := ne_of_gt Q.2.2.1
  have haR : (Q.1.a : ℝ) ≠ 0 := by exact_mod_cast haZ
  rw [rawCMPoint, Complex.div_im]
  simp
  field_simp
/-- In the paper's positive-discriminant range, the canonical point lies in `ℍ`. Positivity of `a` comes from the definition of `rawOrientedForms`. -/ theorem rawCMPoint_im_pos {n r : ℕ} (hn : 0 < n) (Q : RawOrientedForm n r) : 0 < (rawCMPoint Q).im := by
  rw [rawCMPoint_im]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha : 0 < Q.1.a := Q.2.2.1
  exact div_pos hsqrt (by positivity)
/-- The actual upper-half-plane CM point of a raw oriented form. -/ def rawCMUpperHalfPlane {n r : ℕ} (hn : 0 < n) (Q : RawOrientedForm n r) : UpperHalfPlane := ⟨rawCMPoint Q, rawCMPoint_im_pos hn Q⟩
/-- Values of a function on raw CM points are invariant under one concrete `Γ₀(6)` change of variables. This is the exact hypothesis needed for descent, not an arbitrary function on the quotient. -/ def RawCMValueInvariant {n r : ℕ} (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ (hn : 0 < n) (Q Q' : RawOrientedForm n r), gammaZeroSixRelated n r Q Q' → F (rawCMUpperHalfPlane hn Q) = F (rawCMUpperHalfPlane hn Q')
/-- One-step invariance extends to the equivalence closure defining the actual orientation classes. -/ theorem rawCMValue_eq_of_eqvGen {n r : ℕ} (F : UpperHalfPlane → ℂ) (hF : RawCMValueInvariant (n := n) (r := r) F) (hn : 0 < n) {Q Q' : RawOrientedForm n r} (h : Relation.EqvGen (gammaZeroSixRelated n r) Q Q') : F (rawCMUpperHalfPlane hn Q) = F (rawCMUpperHalfPlane hn Q') := by
  exact Relation.EqvGen.recOn h (fun x y hxy => hF hn x y hxy) (fun _ => rfl) (fun _ _ _ ih => ih.symm) (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
/-- The value induced on the actual quotient of oriented forms. -/ def orientedCMValue {n r : ℕ} (F : UpperHalfPlane → ℂ) (hF : RawCMValueInvariant (n := n) (r := r) F) (hn : 0 < n) : orientedForms n r → ℂ :=
  Quotient.lift (fun Q : RawOrientedForm n r => F (rawCMUpperHalfPlane hn Q)) (fun _ _ h => rawCMValue_eq_of_eqvGen F hF hn h)
/-- Rolen's genuine eta-quotient value on the actual oriented form classes. -/ def actualOrientedHauptmodulValue {n r : ℕ} (hInv : RawCMValueInvariant (n := n) (r := r) analyticHauptmodul) (hn : 0 < n) : orientedForms n r → ℂ := orientedCMValue analyticHauptmodul hInv hn
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
def awaySixToRat : SptCM.AwaySix →+* ℚ := Localization.awayLift (Int.castRingHom ℚ) 6 (by norm_num)
/-- The canonical `ℤ[1/6]`-algebra structure on every rational algebra. -/ instance awaySixAlgebra (L : Type*) [CommRing L] [Algebra ℚ L] : Algebra SptCM.AwaySix L := ((algebraMap ℚ L).comp awaySixToRat).toAlgebra
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open Polynomial
/-- The four actual finite oriented-class sets together with their CM points. The coordinates are not fields: below they are defined by evaluating the actual Dedekind-eta Hauptmodul at these points. -/ structure ActualOrientedCMCoordinates (n h : ℕ) where
  orientation1 : OrientedCMEnumeration n 1 h
  orientation11 : OrientedCMEnumeration n 11 h
  orientation5 : OrientedCMEnumeration n 5 h
  orientation7 : OrientedCMEnumeration n 7 h
  n_pos : 0 < n
  invariant1 : RawCMValueInvariant (n := n) (r := 1) analyticHauptmodul
  invariant11 : RawCMValueInvariant (n := n) (r := 11) analyticHauptmodul
  invariant5 : RawCMValueInvariant (n := n) (r := 5) analyticHauptmodul
  invariant7 : RawCMValueInvariant (n := n) (r := 7) analyticHauptmodul
/-- Sound I16 output: polynomials over `ℤ[1/6]` whose complex images are literally the two actual analytic root products. In particular this contains no claim that an individual algebraic CM value lies in `ℤ[1/6]`. -/ structure ActualClassPolynomialSpec {n h : ℕ} (C : ActualOrientedCMCoordinates n h) where
  A : AwaySix[X]
  B : AwaySix[X]
  mapA :
    A.map awaySixToComplex =
      classPolynomial
        (fun i : C.orientation1.Index ⊕ C.orientation11.Index =>
          match i with
          | .inl j => actualOrientedHauptmodulValue C.invariant1 C.n_pos (C.orientation1.classes j)
          | .inr j => actualOrientedHauptmodulValue C.invariant11 C.n_pos (C.orientation11.classes j))
  mapB :
    B.map awaySixToComplex =
      classPolynomial
        (fun i : C.orientation5.Index ⊕ C.orientation7.Index =>
          match i with
          | .inl j => actualOrientedHauptmodulValue C.invariant5 C.n_pos (C.orientation5.classes j)
          | .inr j => actualOrientedHauptmodulValue C.invariant7 C.n_pos (C.orientation7.classes j))
  monicA : A.Monic
  monicB : B.Monic
namespace ActualOrientedCMCoordinates
variable {n h : ℕ} (C : ActualOrientedCMCoordinates n h)
/-- The actual analytic Hauptmodul roots in numerator orientations. -/ def numeratorRoot : C.orientation1.Index ⊕ C.orientation11.Index → ℂ
  | .inl i => actualOrientedHauptmodulValue C.invariant1 C.n_pos (C.orientation1.classes i)
  | .inr i => actualOrientedHauptmodulValue C.invariant11 C.n_pos (C.orientation11.classes i)
/-- The actual analytic Hauptmodul roots in denominator orientations. -/ def denominatorRoot : C.orientation5.Index ⊕ C.orientation7.Index → ℂ
  | .inl i => actualOrientedHauptmodulValue C.invariant5 C.n_pos (C.orientation5.classes i)
  | .inr i => actualOrientedHauptmodulValue C.invariant7 C.n_pos (C.orientation7.classes i)
/-- A finite Galois class field containing all actual CM values. The only CM input is the standard reciprocity action on these algebraic values; rational coefficient descent is proved below by Mathlib's Galois fixed-field theorem. -/ structure FiniteGaloisRealization (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] where
  embedding : L →ₐ[ℚ] ℂ
  embedding_injective : Function.Injective embedding
  numeratorAlgebraicRoot : C.orientation1.Index ⊕ C.orientation11.Index → L
  denominatorAlgebraicRoot : C.orientation5.Index ⊕ C.orientation7.Index → L
  realizesNumerator : ∀ i, embedding (numeratorAlgebraicRoot i) = C.numeratorRoot i
  realizesDenominator : ∀ i, embedding (denominatorAlgebraicRoot i) = C.denominatorRoot i
  numeratorPermutation : ∀ _σ : L ≃ₐ[ℚ] L, C.orientation1.Index ⊕ C.orientation11.Index ≃ C.orientation1.Index ⊕ C.orientation11.Index
  denominatorPermutation : ∀ _σ : L ≃ₐ[ℚ] L, C.orientation5.Index ⊕ C.orientation7.Index ≃ C.orientation5.Index ⊕ C.orientation7.Index
  numerator_reciprocity : ∀ (σ : L ≃ₐ[ℚ] L) i, σ (numeratorAlgebraicRoot i) = numeratorAlgebraicRoot (numeratorPermutation σ i)
  denominator_reciprocity : ∀ (σ : L ≃ₐ[ℚ] L) i, σ (denominatorAlgebraicRoot i) = denominatorAlgebraicRoot (denominatorPermutation σ i)
/-- The good-reduction refinement of a finite-Galois realization: every algebraic CM representative is integral over `ℤ[1/6]`. Notice that this says that the roots lie in the integral closure inside `L`, not that they themselves lie in `ℤ[1/6]`. -/ structure IntegralFiniteGaloisRealization (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] extends C.FiniteGaloisRealization L where
  integralNumerator : ∀ i, IsIntegral AwaySix (toFiniteGaloisRealization.numeratorAlgebraicRoot i)
  integralDenominator : ∀ i, IsIntegral AwaySix (toFiniteGaloisRealization.denominatorAlgebraicRoot i)
namespace FiniteGaloisRealization
variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] (F : C.FiniteGaloisRealization L)
end FiniteGaloisRealization
namespace IntegralFiniteGaloisRealization
variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
end IntegralFiniteGaloisRealization
end ActualOrientedCMCoordinates
end
end SptCM.CM.Repaired
namespace SptCM.Repair
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
/-- A Laurent series whose coefficient at `-1` is one (and which has no terms below `-1`) is transcendental over its coefficient field. -/ theorem laurentSeries_transcendental_of_simple_pole {K : Type*} [Field K] (t : LaurentSeries K) (hcoeff : t.coeff (-1) = 1) (_hbelow : ∀ z : ℤ, z < -1 → t.coeff z = 0) : Transcendental K t := by
  letI : Valuation.IsTrivialOn K (Valued.v : Valuation (LaurentSeries K) _) :=
    Valuation.IsTrivialOn.of_le_one Valued.v fun a =>
      (LaurentSeries.val_le_one_iff_eq_coe K _).mpr
        ⟨PowerSeries.C a, by
          rw [LaurentSeries.algebraMap_apply]
          exact HahnSeries.ofPowerSeries_C a⟩
  apply Valuation.transcendental_of_ne_one (v := (Valued.v : Valuation (LaurentSeries K) _)) K t
  · intro ht
    have hz : t.coeff (-1) = 0 := ht ▸ HahnSeries.coeff_zero
    exact one_ne_zero (hcoeff.symm.trans hz)
  · intro hv
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe K t).mp (le_of_eq hv)
    have hz : (F : LaurentSeries K).coeff (-1) = 0 :=
      (PowerSeries.coeff_coe (f := F) (-1)).trans (if_pos (Int.negSucc_lt_zero 0))
    exact zero_ne_one (hz.symm.trans
      ((congrArg (fun f : LaurentSeries K => f.coeff (-1)) hF).trans hcoeff))

end SptCM.Repair
namespace SptCM.Repair
/-- The principal part `t(q) = q⁻¹ - 5 + O(q)` of the level-six Hauptmodul. -/ def HasHauptmodulPrincipalPart {K : Type*} [Ring K] (t : LaurentSeries K) : Prop := t.coeff (-1) = 1 ∧ t.coeff 0 = -5 ∧ ∀ z : ℤ, z < -1 → t.coeff z = 0
end SptCM.Repair
namespace SptCM.Repair
open scoped PowerSeries
/-- The contribution of the `m`-th Euler index to the unit part of `η(τ)^5 η(3τ) / (η(2τ) η(6τ)^5)`. -/ noncomputable def hauptmodulFormalEulerFactor (m : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ m) ^ 5 * (1 - PowerSeries.X ^ (3 * m)) * PowerSeries.subst (PowerSeries.X ^ (2 * m)) (PowerSeries.invOneSubPow ℤ 1 : PowerSeries ℤ) * PowerSeries.subst (PowerSeries.X ^ (6 * m)) (PowerSeries.invOneSubPow ℤ 5 : PowerSeries ℤ)
/-- The coefficientwise stabilized formal Euler product for the level-six Hauptmodul's unit part. Degree `d` is read from the first `d+2` positive Euler indices, after which no omitted factor can affect it. -/ noncomputable def hauptmodulFormalEulerUnit : PowerSeries ℤ :=
  PowerSeries.mk fun d => PowerSeries.coeff d (∏ i ∈ Finset.range (d + 2), hauptmodulFormalEulerFactor (i + 1))
/-- The formal Laurent series obtained by adjoining the net `q⁻¹` prefactor to the formal Euler unit. This is not asserted to be the analytic eta quotient's Laurent expansion. -/ noncomputable def hauptmodulFormalLaurent : LaurentSeries ℤ := HahnSeries.single (-1) 1 * (hauptmodulFormalEulerUnit : LaurentSeries ℤ)
theorem hauptmodulFormalEulerUnit_coeff_zero : PowerSeries.coeff 0 hauptmodulFormalEulerUnit = 1 := by
  simp only [hauptmodulFormalEulerUnit, PowerSeries.coeff_mk]
  norm_num [hauptmodulFormalEulerFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, PowerSeries.invOneSubPow, Finset.prod_range_succ]
theorem hauptmodulFormalEulerUnit_coeff_one : PowerSeries.coeff 1 hauptmodulFormalEulerUnit = -5 := by
  simp only [hauptmodulFormalEulerUnit, PowerSeries.coeff_mk]
  norm_num [hauptmodulFormalEulerFactor, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, PowerSeries.invOneSubPow, Finset.prod_range_succ]
theorem hauptmodulFormalLaurent_principalPart : HasHauptmodulPrincipalPart hauptmodulFormalLaurent := by
  refine ⟨?_, ?_, ?_⟩
  · change (HahnSeries.single (-1) 1 * (hauptmodulFormalEulerUnit : LaurentSeries ℤ)).coeff ((0 : ℤ) + (-1)) = 1
    rw [HahnSeries.coeff_single_mul_add]
    simpa [PowerSeries.coeff_coe] using hauptmodulFormalEulerUnit_coeff_zero
  · change (HahnSeries.single (-1) 1 * (hauptmodulFormalEulerUnit : LaurentSeries ℤ)).coeff ((1 : ℤ) + (-1)) = -5
    rw [HahnSeries.coeff_single_mul_add]
    simpa [PowerSeries.coeff_coe] using hauptmodulFormalEulerUnit_coeff_one
  · intro z hz
    have hz' : z + 1 < 0 := lt_sub_iff_add_lt.mp hz
    unfold hauptmodulFormalLaurent
    rw [← show (z + 1) + (-1) = z from add_neg_cancel_right z 1]
    rw [HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    simp [hz']
end SptCM.Repair
@[expose] public section
namespace SptCM.Analytic.Repaired
open Polynomial
noncomputable section
/-- The full finite divisor of a rational function in the Hauptmodul coordinate. The argument is the actual complex point, not its orientation. The zero function is excluded whenever this divisor is used for rigidity. -/ def rationalFunctionDivisor (f : RatFunc ℚ) (z : ℂ) : ℤ :=
  ((f.num.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ) - ((f.denom.map (algebraMap ℚ ℂ)).rootMultiplicity z : ℤ)
end
end SptCM.Analytic.Repaired
end
@[expose] public section
namespace SptCM.Analytic.Repaired
noncomputable section
/-- Cusp representatives in the order infinity, zero, one-half, one-third. -/ def i12CuspTransform (c : Fin 4) (z : ℂ) : ℂ := if c = 0 then z else if c = 1 then -1 / z else if c = 2 then z / (2 * z + 1) else z / (3 * z + 1)
def i12CuspWidth (c : Fin 4) : ℕ := if c = 0 then 1 else if c = 1 then 6 else if c = 2 then 3 else 2
/-- A genuine analytic realization of a rational-coefficient Laurent series. The unitary transformation law is on Gamma_0(6), and every cusp has a convergent local expansion with a nonvanishing analytic unit. Real orders allow unitary multipliers; zero orders give ordinary holomorphic units. The convergence requirement ties the analytic function to the formal series. -/ structure I12UnitaryMeromorphicRealization (f : LaurentSeries ℚ) where
  toFun : ℂ → ℂ
  meromorphic : MeromorphicOn toFun {z : ℂ | 0 < z.im}
  nonzeroOrder : ∀ z : ℂ, 0 < z.im → meromorphicOrderAt toFun z ≠ ⊤
  unitary : ∀ γ : SptCM.GammaZeroSixMatrix, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z : ℂ, 0 < z.im → toFun (((γ.p : ℂ) * z + γ.q) / ((γ.s : ℂ) * z + γ.t)) = u * toFun z
  expansion : ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im → HasSum (fun k : ℤ => (f.coeff k : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * z)) ^ k) (toFun z)
  cuspOrder : Fin 4 → ℝ
  cuspExpansion : ∀ c : Fin 4, ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧ ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℂ, Y < z.im → toFun (i12CuspTransform c z) = Complex.exp (2 * Real.pi * Complex.I * (cuspOrder c : ℂ) * z / (i12CuspWidth c : ℂ)) * U (Complex.exp (2 * Real.pi * Complex.I * z / (i12CuspWidth c : ℂ)))
def HasI12UnitaryMeromorphicRealization (f : LaurentSeries ℚ) : Prop := Nonempty (I12UnitaryMeromorphicRealization f)
end
end SptCM.Analytic.Repaired
end
namespace SptCM.Analytic.Repaired
open SptCM.RolenLiterature
open Polynomial
/-- The four local orientations occurring in the level-six Heegner divisor. -/ inductive I12Orientation
  | one
  | eleven
  | five
  | seven
  deriving DecidableEq
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- The residue represented by an orientation. -/ def I12Orientation.residue : I12Orientation → Fin 12
  | .one => 1
  | .eleven => 11
  | .five => 5
  | .seven => 7
/-- A divisor supported on the four oriented CM families. -/ abbrev I12Divisor := I12Orientation → ℤ
/-- The divisor read directly from the coefficient at the unique negative index of the vector-valued input. -/ def heegnerDivisorFromSeries (n : ℕ) (V : ℤ → Fin 12 → ℤ) : I12Divisor := fun o => V (-(n : ℤ)) o.residue
/-- The canonical embedding of `ℤ[1/6]` into `ℚ`. -/ noncomputable def awaySixToRat : SptCM.AwaySix →+* ℚ := Localization.awayLift (Int.castRingHom ℚ) 6 (by norm_num)
/-- The actual Laurent-series evaluation of `A_n(t)/B_n(t)`. The coefficient polynomials come from a sound descent specification for the genuine complex root products, and substitution is Mathlib's `aeval`. -/ noncomputable def actualClassPolynomialLaurentQuotient {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h} (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C) (t : LaurentSeries ℚ) : LaurentSeries ℚ :=
  Polynomial.aeval t (D.A.map awaySixToRat) / Polynomial.aeval t (D.B.map awaySixToRat)
/-- The actual stabilized Euler quotient attached to the scalar series of the I10 input. These are precisely the canonical products constructed in I14. -/ noncomputable def actualBorcherdsEulerQuotient {Form : Type*} (F : FourComponentInput Form) : LaurentSeries ℚ :=
  ((SptCM.Repair.eulerProductPlus F.scalarSeries : PowerSeries ℚ) : LaurentSeries ℚ) / ((SptCM.Repair.eulerProductMinus F.scalarSeries : PowerSeries ℚ) : LaurentSeries ℚ)
/-- The exact integral Euler-product Hauptmodul, base-changed to `ℚ` for the characteristic-zero class-polynomial quotient. -/ noncomputable def actualRationalHauptmodulLaurent : LaurentSeries ℚ := HahnSeries.map SptCM.Repair.hauptmodulFormalLaurent (Int.castRingHom ℚ)
/-- The rational base change retains the exact principal part `q⁻¹ - 5 + O(q)`. -/ theorem actualRationalHauptmodulLaurent_principalPart : SptCM.Repair.HasHauptmodulPrincipalPart actualRationalHauptmodulLaurent :=
  by
  rcases SptCM.Repair.hauptmodulFormalLaurent_principalPart with ⟨hneg, hzero, hbelow⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [actualRationalHauptmodulLaurent, HahnSeries.map_coeff] using congrArg (fun x : ℤ => (x : ℚ)) hneg
  · simpa [actualRationalHauptmodulLaurent, HahnSeries.map_coeff] using congrArg (fun x : ℤ => (x : ℚ)) hzero
  · intro z hz
    rw [actualRationalHauptmodulLaurent, HahnSeries.map_coeff, hbelow z hz]
    simp
/-- The embedding of the rational function field in the genuine formal Hauptmodul. Its simple pole proves transcendence, so this is an injective algebra homomorphism, not an arbitrary interpretation of formal series. -/ noncomputable def rationalHauptmodulExpansion : RatFunc ℚ →+* LaurentSeries ℚ :=
  IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) (L := LaurentSeries ℚ) (g := (Polynomial.aeval actualRationalHauptmodulLaurent).toRingHom)
    (by exact transcendental_iff_injective.mp (SptCM.Repair.laurentSeries_transcendental_of_simple_pole actualRationalHauptmodulLaurent actualRationalHauptmodulLaurent_principalPart.1 actualRationalHauptmodulLaurent_principalPart.2.2))
/-- The complete divisor of a single oriented CM family, retaining the Hauptmodul coordinate of every point and its multiplicity. -/ noncomputable def orientedCMPointDivisor {n h : ℕ} (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h) (o : I12Orientation) (z : ℂ) : ℤ :=
  match o with
  | .one => (classPolynomial (fun i : C.orientation1.Index => SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant1 C.n_pos (C.orientation1.classes i))).rootMultiplicity z
  | .eleven => (classPolynomial (fun i : C.orientation11.Index => SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant11 C.n_pos (C.orientation11.classes i))).rootMultiplicity z
  | .five => (classPolynomial (fun i : C.orientation5.Index => SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant5 C.n_pos (C.orientation5.classes i))).rootMultiplicity z
  | .seven => (classPolynomial (fun i : C.orientation7.Index => SptCM.CM.Repaired.actualOrientedHauptmodulValue C.invariant7 C.n_pos (C.orientation7.classes i))).rootMultiplicity z
noncomputable def fullHeegnerDivisor {n h : ℕ} (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h) (a : I12Divisor) (z : ℂ) : ℤ := a .one * orientedCMPointDivisor C .one z + a .eleven * orientedCMPointDivisor C .eleven z + a .five * orientedCMPointDivisor C .five z + a .seven * orientedCMPointDivisor C .seven z
/-- Interior divisors are functions of actual complex coordinates. Cusp orders are real because a unitary character can have nonintegral exponents. The compatibility law is needed only when every cusp order is zero. -/ structure I12MeromorphicGeometry where
  divisor : LaurentSeries ℚ → ℂ → ℤ
  cuspData : LaurentSeries ℚ → Fin 4 → ℝ
  analyticCuspOrders : ∀ f (R : I12UnitaryMeromorphicRealization f), cuspData f = R.cuspOrder
  analyticDivisor : ∀ f (R : I12UnitaryMeromorphicRealization f) (τ : UpperHalfPlane), divisor f (SptCM.CM.Repaired.analyticHauptmodul τ) = (meromorphicOrderAt R.toFun (τ : ℂ)).untop₀
  rationalDivisor : ∀ r : RatFunc ℚ, r ≠ 0 → cuspData (rationalHauptmodulExpansion r) = 0 → divisor (rationalHauptmodulExpansion r) = rationalFunctionDivisor r
/-- Explicit analytic descent input: a nonzero weight-zero meromorphic form with unitary character and zero cusp orders on the compact genus-zero curve is rational in its Hauptmodul. The analytic domain is fixed by convergent expansions and actual meromorphic functions, rather than a caller-selected predicate. This general descent theorem remains an explicit analytic input; it involves no CM polynomials or target identity. -/ def I12GenusZeroDescentPrinciple (G : I12MeromorphicGeometry) : Prop :=
  ∀ f, HasI12UnitaryMeromorphicRealization f → G.cuspData f = 0 → f ≠ 0 → ∃ r : RatFunc ℚ, rationalHauptmodulExpansion r = f
/-- The finite CM roots are interior points, and the monic equal-degree quotient has no zero or pole at any cusp. -/ def I12ClassPolynomialCuspPrinciple (G : I12MeromorphicGeometry) : Prop :=
  ∀ {n h : ℕ} {C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h} (D : SptCM.CM.Repaired.ActualClassPolynomialSpec C), G.cuspData (actualClassPolynomialLaurentQuotient D actualRationalHauptmodulLaurent) = 0
def I12WeylCuspPrinciple {Form : Type*} (G : I12MeromorphicGeometry) (lift : FourComponentInput Form → LaurentSeries ℚ) (weylVector : FourComponentInput Form → ℕ → ℂ) : Prop := ∀ F, (∀ c, IsLevelSixDivisor c → weylVector F c = 0) → G.cuspData (lift F) = 0
/-- E5 with the full Heegner divisor, applied after all Weyl vectors vanish. -/ noncomputable def actualI12BorcherdsModel {Form : Type*} [SMul ℂ Form] (E : EtaJGeneratorBasis Form) {n h : ℕ} (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h) (lift : FourComponentInput Form → LaurentSeries ℚ) (divisor : LaurentSeries ℚ → ℂ → ℤ)
    (weylVector : FourComponentInput Form → ℕ → ℂ) : BorcherdsLiftModel (FourComponentInput Form) (LaurentSeries ℚ) (ℂ → ℤ)
    where
  admissibleInput := fun F => VectorInputSpec E n F ∧ (∀ c, IsLevelSixDivisor c → weylVector F c = 0)
  lift := lift
  divisor := divisor
  predictedDivisor := fun F => fullHeegnerDivisor C (heegnerDivisorFromSeries n F.vectorSeries)
  hasUnitaryCharacter := HasI12UnitaryMeromorphicRealization
  hasProductExpansion := fun F g => g = actualBorcherdsEulerQuotient F
end SptCM.Analytic.Repaired
namespace SptCM.Analytic.Repaired
open SptCM.RolenLiterature
noncomputable section
/-- Uniform analytic source data for the actual auxiliary forms. All fields are either general external theorems (E3, E5, E6 and the finite-height Stokes principle) or application comparisons between the concrete models. In particular, this structure has no field asserting a product identity, Wronskian statement, polynomial separation, or prime classification. -/ structure UniformActualNormalizedProductPackage (Form Completion Series V : Type*) [SMul ℂ Form] [AddCommMonoid V] [Module ℂ V] (E : EtaJGeneratorBasis Form) where
  harmonicMaass : HarmonicMaassModel Completion Series
  mockSeries : Series
  etaSeries : Series
  shadowNormalization : Series → Series
  bringmann : BringmannCompletion harmonicMaass mockSeries etaSeries shadowNormalization
  stokesQualified : HnStokesInput Completion → Prop
  truncatedIntegral : HnStokesInput Completion → ℕ → ℝ
  topBoundaryError : HnStokesInput Completion → ℕ → ℝ
  regularizedValue : HnStokesInput Completion → ℝ
  qualification : ∀ (k : ℕ) (F : Completion), harmonicMaass.holomorphicPart F = mockSeries → harmonicMaass.shadow F = shadowNormalization etaSeries → stokesQualified (actualHnStokesInput E.toEtaJPowerBasis k F)
  finiteHeightStokes : FiniteHeightStokesTheorem (hnFiniteHeightStokesModel stokesQualified truncatedIntegral topBoundaryError regularizedValue)
  lift : FourComponentInput Form → LaurentSeries ℚ
  geometry : I12MeromorphicGeometry
  weylVector : FourComponentInput Form → ℕ → ℂ
  bruinierOno : ∀ {n h : ℕ} (C : SptCM.CM.Repaired.ActualOrientedCMCoordinates n h), E5BruinierOno (actualI12BorcherdsModel E C lift geometry.divisor weylVector)
  pairing : FourComponentInput Form → V →ₗ[ℂ] ℂ
  componentTheta : Fin 12 → V
  etaTheta : V
  normalization : ℂ → ℂ
  bruinierSchwagenscheidt : ∀ n : ℕ, E6BruinierSchwagenscheidt (componentWeylVectorModel (VectorInputSpec E n) weylVector pairing componentTheta normalization)
  etaComponentIdentity : EtaComponentThetaIdentity componentTheta etaTheta
  normalization_zero : normalization 0 = 0
  pairingComparison :
    ∀ (k : ℕ) (F : Completion), harmonicMaass.holomorphicPart F = mockSeries → harmonicMaass.shadow F = shadowNormalization etaSeries → pairing (auxiliaryFourComponentInput E k (aCoeff ((24 * k - 1 : ℕ) : ℤ))) etaTheta = (regularizedValue (actualHnStokesInput E.toEtaJPowerBasis k F) : ℂ)
  genusZeroDescent : I12GenusZeroDescentPrinciple geometry
  classPolynomialCusp : I12ClassPolynomialCuspPrinciple geometry
  weylCusp : I12WeylCuspPrinciple geometry lift weylVector
end
end SptCM.Analytic.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open SptCM.RolenLiterature
/-- A function on the upper half-plane obeys the level-six modular transformation law on CM points. This is the source-faithful E4/E7 boundary: it is uniform in the discriminant and orientation, and says only that the function is unchanged by a single `Γ₀(6)` change of variables. -/ def GammaZeroSixCMTransformationLaw (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ {n r : ℕ} (hn : 0 < n) (Q : RawOrientedForm n r) (g : GammaZeroSixMatrix) (hmem : transformQuadraticForm g Q.1 ∈ rawOrientedForms n r), F (rawCMUpperHalfPlane hn Q) = F (rawCMUpperHalfPlane hn (⟨transformQuadraticForm g Q.1, hmem⟩ : RawOrientedForm n r))
/-- The exact E4/E7 application needed here: Rolen's eta quotient has the level-six transformation law. This proposition is the smallest additional literature input absent from the older predicate-only E4/E7 models. -/ abbrev E4E7AnalyticHauptmodulTransformation : Prop := GammaZeroSixCMTransformationLaw analyticHauptmodul
end
end SptCM.CM.Repaired
namespace SptCM.RolenLiterature.Repair
noncomputable section
open SptCM.CM.Repaired
/-- A good-prime residue map is defined on the integral closure, not on the whole number field. Compatibility says that it extends the chosen reduction of `ℤ[1/6]` coefficientwise. -/ structure E8IntegralClosureResidueSpecialization (L k : Type*) (ℓ : ℕ) [Field L] [Algebra AwaySix L] [Field k] [Algebra (ZMod ℓ) k] (coefficientReduction : AwaySix →+* ZMod ℓ) where
  residue : integralClosure AwaySix L →+* k
  compatible : residue.comp (algebraMap AwaySix (integralClosure AwaySix L)) = (algebraMap (ZMod ℓ) k).comp coefficientReduction
run_cmd
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env { }
/-- Additional unproved E8 lying-over/residue application input in precisely the good-prime coefficient ring needed by the paper. The theorem only produces a residue map on the integral closure. Root collisions and polynomial separation are not part of this external statement. -/ def E8AwaySixIntegralClosureResidueTheorem : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (h6 : IsUnit (6 : ZMod ℓ)) (L : Type) (_ : Field L) (_ : Algebra AwaySix L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L), Nonempty (E8IntegralClosureResidueSpecialization L (AlgebraicClosure (ZMod ℓ)) ℓ (SptCM.awaySixReduction ℓ h6))
/-- Atomic public ledger entries which are already independent of any choice of analytic or geometric model. The more elaborate E3--E9 and E11 results remain parameterized by their source models in `RolenLiterature`; this record must not turn those application models into arbitrary universally quantified claims. -/ structure UniformArithmeticLiterature where
  e1 : E1AndrewsCongruences
  e2Finite : E2AhlgrenKimFiniteExclusion
  e2ThetaCycle : E2AhlgrenKimThetaCycle
  e8Residue : E8AwaySixIntegralClosureResidueTheorem
  e10 : E10TrevinoCorrected
  e11SquarefreeCusps : SquarefreeGammaZeroCuspClassification
end
end SptCM.RolenLiterature.Repair
namespace SptCM.Repair
open scoped ModularForm PowerSeries
/-- A concrete integral unit expansion of an analytic function at infinity. The power series is integral, is a unit with constant coefficient one, and its complex evaluation on every upper-half-plane nome gives the analytic function after adjoining the simple pole `q⁻¹`. -/ def HasActualIntegralUnitExpansion (f : UpperHalfPlane → ℂ) (u : PowerSeries ℤ) : Prop :=
  (∀ τ : UpperHalfPlane, f τ = (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ * (∑' n : ℕ, ((PowerSeries.coeff n u : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ n)) ∧ PowerSeries.coeff 0 u = 1 ∧ IsUnit u
end SptCM.Repair
namespace SptCM.Repair
open scoped ModularForm PowerSeries
/-- Exact application checks for the standard integral model of `X₀(6)` over `ℤ[1/6]`. This is the permissible E7 boundary: it exposes the model and its standard comparison laws but does not assume that the Hauptmodul is a degree-one coordinate. -/ structure ActualX0SixApplicationChecks where
  Cusp : Type
  Curve : Type
  Divisor : Type
  M : SptCM.RolenLiterature.LigozatModel SptCM.CM.Repaired.LevelSixEtaExponents (UpperHalfPlane → ℂ) Cusp ℚ Curve
  G : SptCM.RolenLiterature.IntegralCurveFunctionGeometry (UpperHalfPlane → ℂ) Divisor Curve Cusp (PowerSeries ℤ)
  X : Curve
  zero : Cusp
  oneHalf : Cusp
  oneThird : Cusp
  infinity : Cusp
  ligozat : SptCM.RolenLiterature.LigozatEtaQuotients M
  integralModel : SptCM.RolenLiterature.X0SixGoodIntegralModel M
  genusZero : SptCM.RolenLiterature.X0SixGenusZeroFibers M
  disjointCusps : SptCM.RolenLiterature.X0SixDisjointCusps M
  horizontalDivisor : SptCM.RolenLiterature.E7HorizontalDivisorPrinciple G M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers M.isModularFunction M.cuspOrder
  noVerticalComponent : SptCM.RolenLiterature.E7NoVerticalComponentPrinciple G M.isIntegralModelAwayFromLevel M.hasDisjointStandardCuspSections
  degreeOneCriterion : SptCM.RolenLiterature.E7IntegralDegreeOneCriterion G M.isIntegralModelAwayFromLevel M.hasGenusZeroGeometricFibers M.hasDisjointStandardCuspSections
  ligozatConditions : M.ligozatConditions SptCM.CM.Repaired.hauptmodulExponents
  levelSix : M.isLevelSixModularCurve X
  cuspCases : ∀ c : Cusp, c = zero ∨ c = oneHalf ∨ c = oneThird ∨ c = infinity
  quotient_eq_actual : M.quotient SptCM.CM.Repaired.hauptmodulExponents = SptCM.CM.Repaired.analyticHauptmodul
  order_zero : M.orderFormula SptCM.CM.Repaired.hauptmodulExponents zero = SptCM.CM.Repaired.ligozatCuspOrder SptCM.CM.Repaired.hauptmodulExponents 1
  order_oneHalf : M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneHalf = SptCM.CM.Repaired.ligozatCuspOrder SptCM.CM.Repaired.hauptmodulExponents 2
  order_oneThird : M.orderFormula SptCM.CM.Repaired.hauptmodulExponents oneThird = SptCM.CM.Repaired.ligozatCuspOrder SptCM.CM.Repaired.hauptmodulExponents 3
  order_infinity : M.orderFormula SptCM.CM.Repaired.hauptmodulExponents infinity = SptCM.CM.Repaired.ligozatCuspOrder SptCM.CM.Repaired.hauptmodulExponents 6
  analyticNonvanishingInterpretation : ∀ f : UpperHalfPlane → ℂ, (∀ τ, f τ ≠ 0) → G.hasNoInteriorZeroOrPole f X
  integralExpansionInterpretation : ∀ (f : UpperHalfPlane → ℂ) (u : PowerSeries ℤ), HasActualIntegralUnitExpansion f u → G.hasIntegralUnitExpansionAt f infinity u
/-- The proposition-valued exact E7 input: the standard integral model and all comparison maps required by the application exist. -/ def E7ActualX0SixApplicationChecks : Prop := Nonempty ActualX0SixApplicationChecks
end SptCM.Repair
namespace SptCM
universe u
open Polynomial
/-- Reduced norm in an algebra with quaternionic conjugation. -/ def reducedNorm {R : Type*} [Mul R] [Star R] (α : R) : R := α * star α
end SptCM
namespace SptCM.Repair
noncomputable section
open SptCM.RolenLiterature
/-- General arithmetic attached to the integral lattice of a preserving Eichler order. The local-index law is quantified over arbitrary four integral vectors. Thus an application must separately prove that its particular specialized endomorphisms belong to the preserving order and must compute their reduced norms. -/ structure EichlerLatticeArithmetic {Curve Subgroup Order Lattice D : Type*} [DivisionRing D] [Star D] [Algebra ℚ D] (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D) where
  characteristic : Curve → ℕ
  orderLattice : Order → Lattice
  inOrder : Order → D → Prop
  reducedNorm : D → ℚ
  one_mem : ∀ O, inOrder O 1
  mul_mem : ∀ O {x y}, inOrder O x → inOrder O y → inOrder O (x * y)
  reducedNorm_one : reducedNorm 1 = 1
  reducedNorm_mul : ∀ x y, reducedNorm (x * y) = reducedNorm x * reducedNorm y
  reducedNorm_spec : ∀ x, algebraMap ℚ D (reducedNorm x) = SptCM.reducedNorm x
  squaredNorm_eq : ∀ x, EC.squaredNorm x = 2 * (reducedNorm x : ℝ)
  independent_of_linearIndependent : ∀ a b c d, LinearIndependent ℚ ![a, b, c, d] → EC.independent a b c d
  covolume_nonnegative : ∀ a b c d, 0 ≤ EC.covolume (EC.span a b c d)
  /-- The (reduced-discriminant) local index of an Eichler order. -/   localIndex : Order → ℕ
  /-- The local contributions at the primes dividing the level. -/   localIndexAtTwo : Order → ℕ
  localIndexAtThree : Order → ℕ
  /-- The covolume of a maximal order in the ambient quaternion algebra. -/   maximalOrderCovolume : Curve → ℝ
  /-- General local-to-global index factorization for a level-six Eichler order; all local factors away from `2` and `3` are units. -/   levelSix_localIndex_factorization : ∀ O, EC.isEichlerOfLevelSix O → localIndex O = localIndexAtTwo O * localIndexAtThree O
  /-- Preserving the distinguished line at `2` has local index `2`. -/   levelSix_localIndexAtTwo : ∀ O, EC.isEichlerOfLevelSix O → localIndexAtTwo O = 2
  /-- Preserving the distinguished line at `3` has local index `3`. -/   levelSix_localIndexAtThree : ∀ O, EC.isEichlerOfLevelSix O → localIndexAtThree O = 3
  /-- General discriminant normalization for a maximal order in the supersingular quaternion algebra. -/   maximalOrderCovolume_eq_characteristic : ∀ E, maximalOrderCovolume E = characteristic E
  /-- General finite-index scaling law for the lattice of an Eichler order. -/   orderLattice_covolume : ∀ E C, EC.isEichlerOfLevelSix (EC.preservingOrder E C) → EC.covolume (orderLattice (EC.preservingOrder E C)) = localIndex (EC.preservingOrder E C) * maximalOrderCovolume E
  span_covolume_lower : ∀ E C a b c d, EC.independent a b c d → inOrder (EC.preservingOrder E C) a → inOrder (EC.preservingOrder E C) b → inOrder (EC.preservingOrder E C) c → inOrder (EC.preservingOrder E C) d → EC.covolume (orderLattice (EC.preservingOrder E C)) ≤ EC.covolume (EC.span a b c d)
namespace EichlerLatticeArithmetic
end EichlerLatticeArithmetic
end
end SptCM.Repair
namespace SptCM.CM.Repaired
noncomputable section
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
/-- The good-reduction evaluation law for the actual Hauptmodul on oriented CM points. If an integral class-field element has the analytic Hauptmodul value at a raw CM point, then its residue is the regular coordinate of the reduction of that same CM point. This is uniform in the orientation and raw form and contains no collision, action, commutator, covolume, or separation assertion. -/ structure E8ActualHauptmodulGoodReduction {n h ℓ : ℕ} (C : ActualOrientedCMCoordinates n h) {L k Order IdealClass CMPoint Reduction D : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] [Field k] [Algebra (ZMod ℓ) k] [DivisionRing D] [Star D]
    (F : C.IntegralFiniteGaloisRealization L) {coefficientReduction : SptCM.AwaySix →+* ZMod ℓ} (Sres : E8IntegralClosureResidueSpecialization L k ℓ coefficientReduction) (CM : CMTheoryModel Order IdealClass CMPoint Reduction D) (E8Q : E8OrientedQuadraticSpecialization n CM) where
  coordinate : Reduction → k
  coordinate_injective : Function.Injective coordinate
  reduction_evaluation : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r) (z : integralClosure SptCM.AwaySix L), F.embedding z.1 = analyticHauptmodul (rawCMUpperHalfPlane C.n_pos Q) → coordinate (CM.reduction (E8Q.point r Q)) = Sres.residue z
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
namespace ActualOrientedCMCoordinates
variable {n h : ℕ} (C : ActualOrientedCMCoordinates n h)
variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
end ActualOrientedCMCoordinates
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
namespace E8ActualHauptmodulGoodReduction
variable {n h ℓ : ℕ} {C : ActualOrientedCMCoordinates n h} {L k Order IdealClass CMPoint Reduction D : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] [Field k] [Algebra (ZMod ℓ) k] [DivisionRing D] [Star D] {coefficientReduction : SptCM.AwaySix →+* ZMod ℓ}
  {F : C.IntegralFiniteGaloisRealization L} {Sres : E8IntegralClosureResidueSpecialization L k ℓ coefficientReduction} {CM : CMTheoryModel Order IdealClass CMPoint Reduction D} {E8Q : E8OrientedQuadraticSpecialization n CM}
end E8ActualHauptmodulGoodReduction
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
open SptCM.Repair
namespace ActualClassPolynomialSpec
variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h} (Dpoly : ActualClassPolynomialSpec C)
end ActualClassPolynomialSpec
end
end SptCM.CM.Repaired
namespace SptCM.CM.Repaired
noncomputable section
open Polynomial
open SptCM.RolenLiterature
open SptCM.RolenLiterature.Repair
open SptCM.Repair
namespace ActualClassPolynomialSpec
variable {n h : ℕ} {C : ActualOrientedCMCoordinates n h} (Dpoly : ActualClassPolynomialSpec C)
end ActualClassPolynomialSpec
end
end SptCM.CM.Repaired
namespace SptCM.RolenLiterature.Repair
noncomputable section
open SptCM.CM.Repaired
/-- The carrier models supplied by the good-reduction and inertness part of E8 at one eligible prime and discriminant. This record stops strictly before the Eichler-order argument: it contains no subgroup, covolume, collision, separation, or Wronskian datum. -/ structure E8ActualReductionModel {n h ℓ : ℕ} [Fact ℓ.Prime] (C : ActualOrientedCMCoordinates n h) {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L] (F : C.IntegralFiniteGaloisRealization L) (h6 : IsUnit (6 : ZMod ℓ))
    (Sres : E8IntegralClosureResidueSpecialization L (AlgebraicClosure (ZMod ℓ)) ℓ (SptCM.awaySixReduction ℓ h6)) where
  Order : Type
  IdealClass : Type
  CMPoint : Type
  Reduction : Type
  Dq : Type
  [divisionRingDq : DivisionRing Dq]
  [starDq : Star Dq]
  [algebraDq : Algebra ℚ Dq]
  CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq
  standardCM : E8StandardCM CM
  orientedQuadratic : E8OrientedQuadraticSpecialization n CM
  goodReduction : E8ActualHauptmodulGoodReduction C F Sres CM orientedQuadratic
  rawPointInert : ∀ (r : ℕ) (Q : SptCM.RawOrientedForm n r), CM.inertAt ℓ (orientedQuadratic.point r Q)
/-- The source-facing E9 model and the comparison maps which say that its curve, level structure, and preserving order are the ones occurring in the E8 specialization. Its characteristic law is stated for every point of the fiber, and its order comparison for every CM point; the application-specific `hchar`, `hcyclic`, and `hlevelOrder` functions are derived below. The fields are general Arpin/Goren--Lauter and integral-lattice laws. In particular, no distinguished pair of endomorphisms and no volume inequality is stored here. -/ structure E9ActualLevelSixModel {n ℓ : ℕ} {Order IdealClass CMPoint Reduction Dq : Type*} [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq] (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq) (E8Q : E8OrientedQuadraticSpecialization n CM) where
  Subgroup : Type
  Lattice : Type
  covolumeModel : EichlerCovolumeModel Reduction Subgroup (Subring Dq) Lattice Dq
  arpinGorenLauter : E9ArpinGorenLauter covolumeModel
  latticeArithmetic : SptCM.Repair.EichlerLatticeArithmetic covolumeModel
  levelSubgroupAt : CMPoint → Subgroup
  supersingularCompatible : ∀ P, CM.supersingular P → covolumeModel.supersingular P
  fiberCharacteristic : ∀ P, latticeArithmetic.characteristic (CM.reduction P) = ℓ
  cyclicLevelSubgroup : ∀ P, covolumeModel.cyclicOfOrderSix (levelSubgroupAt P)
  preservingOrderComparison : ∀ P, E8Q.levelOrder = covolumeModel.preservingOrder (CM.reduction P) (levelSubgroupAt P)
  inOrderComparison : ∀ O x, latticeArithmetic.inOrder O x ↔ x ∈ O
namespace E9ActualLevelSixModel
variable {n ℓ : ℕ} {Order IdealClass CMPoint Reduction Dq : Type*} [DivisionRing Dq] [Star Dq] [Algebra ℚ Dq] {CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq} {E8Q : E8OrientedQuadraticSpecialization n CM}
end E9ActualLevelSixModel
/-- Public, discriminant-uniform literature data which do not depend on an implementation choice for the analytic Borcherds and quaternionic models. The class-field field is dependent on the *actual* coordinate family. This is essential: it prevents a single unrelated pair of CM-value families from being used for every discriminant. -/ structure UniformRolenLiterature where
  arithmetic : UniformArithmeticLiterature
  e4e7HauptmodulTransformation : E4E7AnalyticHauptmodulTransformation
  e7ActualIntegralCoordinate : SptCM.Repair.E7ActualX0SixApplicationChecks
  e8NegativeQuadraticOrderDomain : ∀ n : ℕ, E8NegativeQuadraticOrderDomain n
  e8ReducedFormClassification : ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)], E8ReducedFormClassification n
  e8FourOrientedFormClassification : ∀ (n : ℕ) [IsDomain (NegativeQuadraticOrder n)], E8FourOrientedFormClassification n
  e8IntegralCMClassField :
    ∀ (n h : ℕ),
      Squarefree n →
        n % 24 = 23 →
          ∀ C : ActualOrientedCMCoordinates n h,
            ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L), Nonempty (E8FiniteGaloisIntegralCMReciprocity AwaySix (C.orientation1.Index ⊕ C.orientation11.Index) (C.orientation5.Index ⊕ C.orientation7.Index) L C.numeratorRoot C.denominatorRoot)
  e8ActualReduction :
    ∀ {n ℓ : ℕ} [Fact ℓ.Prime] (hsquarefree : Squarefree n) (hmod : n % 24 = 23) (hinert : legendreSym ℓ (-(n : ℤ)) = -1) (C : ActualOrientedCMCoordinates n (SptCM.negativeClassNumber n)) (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (F : C.IntegralFiniteGaloisRealization L) (h6 : IsUnit (6 : ZMod ℓ)) (Sres : E8IntegralClosureResidueSpecialization L (AlgebraicClosure (ZMod ℓ)) ℓ (SptCM.awaySixReduction ℓ h6)), Nonempty (E8ActualReductionModel C F h6 Sres)
  e9ActualLevelSix :
    ∀ {n h ℓ : ℕ} [Fact ℓ.Prime] (C : ActualOrientedCMCoordinates n h) (Order IdealClass CMPoint Reduction Dq : Type) (_ : DivisionRing Dq) (_ : Star Dq) (_ : Algebra ℚ Dq) (CM : CMTheoryModel Order IdealClass CMPoint Reduction Dq) (E8Q : E8OrientedQuadraticSpecialization n CM),
      Nonempty (E9ActualLevelSixModel (ℓ := ℓ) CM E8Q)
end
end SptCM.RolenLiterature.Repair
namespace SptCM.Repair
open SptCM.Analytic SptCM.Analytic.Repaired SptCM.CM.Repaired
theorem rolen_spt_classification {Form Product Completion Series V : Type*} [SMul ℂ Form] [AddCommMonoid V] [Module ℂ V] (lit : SptCM.RolenLiterature.Repair.UniformRolenLiterature) (E : EtaJGeneratorBasis Form) (Analytic : UniformActualNormalizedProductPackage Form Completion Series V E)
    (Grid : IntegralGridRealization) (Mult : WeightTwoMultiplicationTheory ℚ Form Product E Grid.rationalGrid) : ∀ ℓ : ℕ, SptCM.CanonicalCongruencePrime ℓ ↔ ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 := by sorry
end SptCM.Repair
