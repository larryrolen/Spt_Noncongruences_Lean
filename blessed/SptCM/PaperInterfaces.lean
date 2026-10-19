import blessed.SptCM.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# External interfaces for the Spt--CM paper

This module contains no mathematical conclusion proved in the paper.  It only
names the exact results imported from cited literature and supplies small,
neutral data models in which the paper's internal deductions can be stated.
Every imported result is a `Prop`; a formal theorem using it must receive a
proof of that proposition as an explicit argument.
-/

namespace SptCM.PaperInterfaces

/-! ## Neutral models -/

/-- A coefficient model for a Laurent or fractional-power series.  The index
normalization (for example, exponents `n / 24`) is carried by the consumer. -/
abbrev CoeffSeries (R : Type*) := ℤ → R

/-- A coefficientwise operator on the neutral series model. -/
abbrev SeriesOperator (R : Type*) := CoeffSeries R → CoeffSeries R

/-- The coefficient of a neutral series at an integral normalized index. -/
def seriesCoeff {R : Type*} (f : CoeffSeries R) (n : ℤ) : R := f n

/-- Abstract data needed to discuss a harmonic completion without building a
full theory of harmonic Maass forms into the interface module. -/
structure HarmonicCompletionModel (H S : Type*) where
  holomorphicPart : H → S
  shadow : H → S

/-- Abstract Hecke operators in dual weights. -/
structure DualWeightHeckeModel (H S : Type*) where
  heckeThreeHalves : ℕ → H → H
  heckeOneHalf : ℕ → S → S
  shadowScale : ℕ → S → S

/-- The output data of a Borcherds lift used by the general product theorem. -/
structure BorcherdsLiftData (Input Divisor Product : Type*) where
  lift : Input → Product
  divisor : Product → Divisor
  predictedDivisor : Input → Divisor
  hasUnitaryCharacter : Product → Prop
  hasProductExpansion : Input → Product → Prop

/-- Abstract data for the Weyl-vector formula at a cusp. -/
structure WeylVectorData (Input Theta Scalar Cusp : Type*) where
  weylVector : Input → Cusp → Scalar
  regularizedPairing : Input → Theta → Scalar
  cuspTheta : Cusp → Theta
  normalization : Scalar → Scalar

/-- The data used to state Ligozat's eta-quotient criterion without fixing a
particular analytic implementation of eta quotients. -/
structure EtaQuotientModel (Exponent Cusp Order Quotient : Type*) where
  conditions : Exponent → Prop
  quotient : Exponent → Quotient
  isWeightZeroModularFunction : Quotient → Prop
  cuspOrder : Quotient → Cusp → Order
  orderFormula : Exponent → Cusp → Order
  hasTrivialCharacter : Quotient → Prop
  characterIsTrivial : Exponent → Prop

/-- A minimal model of level-preserving endomorphism orders. -/
structure LevelEndomorphismModel (Curve Subgroup Order : Type*) where
  supersingular : Curve → Prop
  cyclicOfOrderSix : Curve → Subgroup → Prop
  preservingOrder : Curve → Subgroup → Order
  eichlerLevelSix : Order → Prop

/-- A neutral covolume model for the four-vector Hadamard estimate. -/
structure CovolumeModel (Lattice Vector : Type*) where
  spanLattice : Vector → Vector → Vector → Vector → Lattice
  linearlyIndependent : Vector → Vector → Vector → Vector → Prop
  covolume : Lattice → ℝ
  squaredNorm : Vector → ℝ

/-! ## Andrews and Ahlgren--Kim -/

/-- Andrews' congruence at `5`. -/
def Andrews5 : Prop := CanonicalCongruencePrime 5

/-- Andrews' congruence at `7`. -/
def Andrews7 : Prop := CanonicalCongruencePrime 7

/-- Andrews' congruence at `13`. -/
def Andrews13 : Prop := CanonicalCongruencePrime 13

/-- The exact finite-range classification furnished by Ahlgren--Kim,
Theorem 3, at the cutoff used in the paper. -/
def AhlgrenKimFiniteExclusion : Prop :=
  ∀ ℓ : ℕ, CanonicalCongruencePrime ℓ → ℓ < 10 ^ 11 →
    ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13

/-- Ahlgren--Kim Proposition 6 after choosing the scalar normalization but
before taking coefficientwise consequences. -/
def AhlgrenKimThetaCycleInput (ℓ : ℕ)
    (thetaPower : SeriesOperator (ZMod ℓ))
    (epsilon : ZMod ℓ) (f : CoeffSeries (ZMod ℓ)) : Prop :=
  thetaPower f = epsilon • f

/-! ## Harmonic Maass forms, eta, and Hecke operators -/

/-- Bringmann's existence and shadow normalization for the completion of the
smallest-parts mock modular form. -/
def BringmannCompletionInput {H S : Type*}
    (M : HarmonicCompletionModel H S) (f eta : S) (shadowConstant : S → S) : Prop :=
  ∃ fhat : H,
    M.holomorphicPart fhat = f ∧ M.shadow fhat = shadowConstant eta

/-- Euler's theta-series identity for Dedekind eta in a chosen series model. -/
def EulerEtaThetaIdentity {S : Type*} (eta thetaSeries : S) : Prop :=
  eta = thetaSeries

/-- The dual-weight Hecke/shadow intertwining formula cited as HMFBook
(7.5), including its normalization factor. -/
def HeckeShadowIntertwiningInput {H S : Type*}
    (M : HarmonicCompletionModel H S) (T : DualWeightHeckeModel H S) : Prop :=
  ∀ (ℓ : ℕ) (F : H),
    M.shadow (T.heckeThreeHalves ℓ F) =
      T.shadowScale ℓ (T.heckeOneHalf ℓ (M.shadow F))

/-! ## Eta quotients and Borcherds products -/

/-- Ligozat's general eta-quotient modularity, character, and cusp-order
formula.  The concrete exponent vector and its four computed cusp orders are
paper-internal applications of this interface. -/
def LigozatEtaQuotientInput {Exponent Cusp Order Quotient : Type*}
    (M : EtaQuotientModel Exponent Cusp Order Quotient) : Prop :=
  ∀ e : Exponent, M.conditions e →
    M.isWeightZeroModularFunction (M.quotient e) ∧
      (∀ c : Cusp, M.cuspOrder (M.quotient e) c = M.orderFormula e c) ∧
      (M.characterIsTrivial e → M.hasTrivialCharacter (M.quotient e))

/-- Bruinier--Ono Theorem 6.1: the general Borcherds lift has the predicted
divisor, unitary character, and product expansion. -/
def BruinierOnoBorcherdsInput {Input Divisor Product : Type*}
    (B : BorcherdsLiftData Input Divisor Product) : Prop :=
  ∀ F : Input,
    B.divisor (B.lift F) = B.predictedDivisor F ∧
      B.hasUnitaryCharacter (B.lift F) ∧
      B.hasProductExpansion F (B.lift F)

/-- Bruinier--Schwagenscheidt equation (11), expressing each Weyl vector as
the normalized regularized pairing with the cusp theta function. -/
def BruinierSchwagenscheidtWeylInput
    {Input Theta Scalar Cusp : Type*}
    (W : WeylVectorData Input Theta Scalar Cusp) : Prop :=
  ∀ (F : Input) (c : Cusp),
    W.weylVector F c =
      W.normalization (W.regularizedPairing F (W.cuspTheta c))

/-! ## Granular CM specialization interfaces -/

/-- Neutral CM reduction data.  Each predicate records one standard input;
no separation or class-polynomial conclusion is included. -/
structure CMReductionModel (CMPoint Reduction Endomorphism : Type*) where
  hasPotentiallyGoodReduction : CMPoint → Prop
  reduction : CMPoint → Reduction
  isInert : ℕ → Prop
  isSupersingular : Reduction → Prop
  specializedAction : CMPoint → Endomorphism
  actionInjectiveAt : CMPoint → Prop

/-- Potential good reduction of CM points, including extension of the
prime-to-residue-characteristic level structure. -/
def CMPotentialGoodReductionInput {CMPoint Reduction Endomorphism : Type*}
    (M : CMReductionModel CMPoint Reduction Endomorphism) : Prop :=
  ∀ P, M.hasPotentiallyGoodReduction P

/-- Deuring's inert-reduction implication, isolated from the collision
argument that later uses supersingularity. -/
def CMInertReductionSupersingularInput
    {CMPoint Reduction Endomorphism : Type*}
    (M : CMReductionModel CMPoint Reduction Endomorphism) : Prop :=
  ∀ (n : ℕ) (P : CMPoint), M.isInert n →
    M.isSupersingular (M.reduction P)

/-- Injectivity of specialization on the CM order. -/
def CMSpecializedActionInjectiveInput
    {CMPoint Reduction Endomorphism : Type*}
    (M : CMReductionModel CMPoint Reduction Endomorphism) : Prop :=
  ∀ P, M.actionInjectiveAt P

/-! ## Quaternionic inputs -/

/-- Arpin Theorem 3.7 in the only specialization used by the paper. -/
def ArpinEichlerOrderInput {Curve Subgroup Order : Type*}
    (M : LevelEndomorphismModel Curve Subgroup Order) : Prop :=
  ∀ (E : Curve) (C : Subgroup),
    M.supersingular E → M.cyclicOfOrderSix E C →
      M.eichlerLevelSix (M.preservingOrder E C)

/-- The four-vector Hadamard/covolume inequality cited from
Goren--Lauter, Lemma 2.1.1. -/
def GorenLauterHadamardInput {Lattice Vector : Type*}
    (M : CovolumeModel Lattice Vector) : Prop :=
  ∀ a b c d : Vector,
    M.linearlyIndependent a b c d →
      M.covolume (M.spanLattice a b c d) ^ 2 ≤
        M.squaredNorm a * M.squaredNorm b *
          M.squaredNorm c * M.squaredNorm d

/-! ## Treviño's corrected character estimate -/

/-- A character is constant on the `H` consecutive integers beginning at
`a`, expressed without committing to a particular character library. -/
def ConstantOnInterval {R : Type*} (χ : ℤ → R) (a : ℤ) (H : ℕ) : Prop :=
  ∀ i j : ℕ, i < H → j < H → χ (a + i) = χ (a + j)

/-- Treviño's Theorem 1 with the 2017 corrected all-prime constant `3.38`.
`Nonprincipal` records the usual character-theoretic hypothesis. -/
def TrevinoCorrectedCharacterBound {R : Type*}
    (Nonprincipal : ℕ → (ℤ → R) → Prop) : Prop :=
  ∀ (ℓ H : ℕ) (χ : ℤ → R) (a : ℤ),
    ℓ.Prime → Nonprincipal ℓ χ → ConstantOnInterval χ a H →
      (H : ℝ) ≤ 3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ

end SptCM.PaperInterfaces
