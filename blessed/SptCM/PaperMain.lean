import blessed.SptCM.PaperInterfaces
import blessed.SptCM.Analytic.ThetaHecke
import blessed.SptCM.Analytic.DualityPairing
import blessed.SptCM.Analytic.PaperConstructions
import blessed.SptCM.Arithmetic.SmallDiscriminant
import blessed.SptCM.CM.ClassPolynomials
import blessed.SptCM.CM.Borcherds
import blessed.SptCM.Quaternion.Separation
import blessed.SptCM.Lemmas.VolumeArithmetic
import blessed.SptCM.Main

/-!
# Paper-level assembly from granular interfaces

This module assembles the paper-level result from explicit interfaces. The
small-discriminant package is proved from its three internal components.
Analytic and CM inputs not constructed in this project are exposed at
intermediate mathematical boundaries: coefficient support followed by the
Borcherds logarithmic-derivative bridge, and quaternionic noncollision
followed by the integral-coordinate coprimality bridge.
-/

namespace SptCM

open Polynomial

namespace PaperComponents

/-- The diagonal theta power, bundled as the linear map needed by the abstract
Hecke-chain lemma. -/
def thetaPowerSeriesLinearMap (ℓ k : ℕ) [Fact ℓ.Prime] :
    Analytic.QSeries (ZMod ℓ) →ₗ[ZMod ℓ] Analytic.QSeries (ZMod ℓ) where
  toFun := Analytic.thetaPowerSeriesOp ℓ k
  map_add' := by
    intro f g
    funext r
    simp only [Analytic.thetaPowerSeriesOp_apply, Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext r
    simp only [Analytic.thetaPowerSeriesOp_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- Lower-level formal-series and Borcherds-lift data for the exact
obstruction.  The fields contain concrete models, the cited
Ahlgren--Kim/Bruinier--Ono/Weyl inputs, normalization facts, and the elementary
grid recurrence.  In particular, no coefficient vanishing, quotient identity,
derivative vanishing, or Wronskian conclusion is a field. -/
structure InfiniteProductObstructionData
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) where
  index : ℕ → ℕ → ℕ → ℕ
  eplus : ℕ → ℕ → ℕ → ℕ
  eminus : ℕ → ℕ → ℕ → ℕ
  numerator : ∀ ℓ n, PowerSeries (ZMod ℓ)
  denominator : ∀ ℓ n, PowerSeries (ZMod ℓ)
  numeratorProduct : ∀ ℓ n,
    IsStabilizedEulerProduct (numerator ℓ n) (index ℓ n) (eplus ℓ n)
  denominatorProduct : ∀ ℓ n,
    IsStabilizedEulerProduct (denominator ℓ n) (index ℓ n) (eminus ℓ n)
  H : ∀ ℓ n, Analytic.HForm (ZMod ℓ)
  normalization : ∀ ℓ n,
    Analytic.HasHnNormalization n
      (Analytic.aCoeff n : ZMod ℓ) (H ℓ n)
  aK : ∀ ℓ [hp : Fact ℓ.Prime], Analytic.AhlgrenKimThetaCycleFromUInput ℓ
  euler : ∀ ℓ [hp : Fact ℓ.Prime], Analytic.EulerInertMismatchInput ℓ
  chi : ∀ ℓ n, ℕ → ZMod ℓ
  grid : ∀ ℓ n, ℕ → Analytic.HForm (ZMod ℓ)
  gridPrincipalPart : ∀ ℓ n m, 1 < m →
    Analytic.HasGridPrincipalPart (chi ℓ n) m (grid ℓ n m)
  weightTwoResidue : ∀ ℓ n m, 1 < m →
    Analytic.WeightTwoResidueInput n m (H ℓ n) (grid ℓ n m)
  factorChain : ∀ (ℓ n m : ℕ), List ℕ
  factorChain_prod : ∀ (ℓ n m : ℕ), (factorChain ℓ n m).prod = m
  gridBase : ∀ ℓ n [hp : Fact ℓ.Prime],
    Analytic.IsThetaEigen
      (thetaPowerSeriesLinearMap ℓ ((ℓ - 1) / 2))
      (Analytic.thetaCycleEigenvalue ℓ) (grid ℓ n 1)
  gridStep : ∀ ℓ n m p [hp : Fact ℓ.Prime],
    Analytic.IsThetaEigen
      (thetaPowerSeriesLinearMap ℓ ((ℓ - 1) / 2))
      (Analytic.thetaCycleEigenvalue ℓ) (grid ℓ n m) →
    Analytic.IsThetaEigen
      (thetaPowerSeriesLinearMap ℓ ((ℓ - 1) / 2))
      (Analytic.thetaCycleEigenvalue ℓ) (grid ℓ n (m * p))
  exponentIdentity : ∀ ℓ n i,
    (eplus ℓ n i : ZMod ℓ) - (eminus ℓ n i : ZMod ℓ) =
      H ℓ n ((index ℓ n i : ℤ) ^ 2)
  oneSided : ∀ ℓ n i, eplus ℓ n i = 0 ∨ eminus ℓ n i = 0
  t : ∀ ℓ n, PowerSeries (ZMod ℓ)
  tTranscendental : ∀ ℓ n, Transcendental (ZMod ℓ) (t ℓ n)
  thetaT_ne_zero : ∀ ℓ n,
    PowerSeries.derivative (ZMod ℓ) (t ℓ n) ≠ 0
  classDenominator_ne_zero : ∀ ℓ n, aeval (t ℓ n) (B ℓ n) ≠ 0
  denominator_ne_zero : ∀ ℓ n, denominator ℓ n ≠ 0
  Input : ℕ → ℕ → Type
  Divisor : ℕ → ℕ → Type
  Theta : ℕ → ℕ → Type
  Scalar : ℕ → ℕ → Type
  Cusp : ℕ → ℕ → Type
  scalarZero : ∀ ℓ n, Zero (Scalar ℓ n)
  borcherds : ∀ ℓ n, PaperInterfaces.BorcherdsLiftData
    (Input ℓ n) (Divisor ℓ n) (LaurentSeries (ZMod ℓ))
  weyl : ∀ ℓ n,
    PaperInterfaces.WeylVectorData
      (Input ℓ n) (Theta ℓ n) (Scalar ℓ n) (Cusp ℓ n)
  inputForm : ∀ ℓ n, Input ℓ n
  borcherdsInput : ∀ ℓ n,
    PaperInterfaces.BruinierOnoBorcherdsInput (borcherds ℓ n)
  productExpansion_iff : ∀ ℓ n [hp : Fact ℓ.Prime]
      (g : LaurentSeries (ZMod ℓ)),
    (borcherds ℓ n).hasProductExpansion (inputForm ℓ n) g ↔
      g = (numerator ℓ n : LaurentSeries (ZMod ℓ)) /
        (denominator ℓ n : LaurentSeries (ZMod ℓ))
  weylInput : ∀ ℓ n,
    PaperInterfaces.BruinierSchwagenscheidtWeylInput (weyl ℓ n)
  classDivisor : ∀ ℓ n, Divisor ℓ n
  leadingValue : ∀ ℓ n, LaurentSeries (ZMod ℓ) → ZMod ℓ
  pairing_zero : ∀ ℓ n (c : Cusp ℓ n),
    (weyl ℓ n).regularizedPairing (inputForm ℓ n)
      ((weyl ℓ n).cuspTheta c) = 0
  normalization_zero : ∀ ℓ n, (weyl ℓ n).normalization 0 = 0
  predicted_divisor : ∀ ℓ n,
    (borcherds ℓ n).predictedDivisor (inputForm ℓ n) = classDivisor ℓ n
  CuspExponentsVanish : ℕ → ℕ → Prop
  cusp_of_weyl : ∀ ℓ n,
    (∀ c : Cusp ℓ n,
      (weyl ℓ n).weylVector (inputForm ℓ n) c = 0) →
      CuspExponentsVanish ℓ n
  rigidity : ∀ ℓ n [hp : Fact ℓ.Prime],
    (borcherds ℓ n).divisor
      ((borcherds ℓ n).lift (inputForm ℓ n)) = classDivisor ℓ n →
    CuspExponentsVanish ℓ n →
    ∃ c : ZMod ℓ, (borcherds ℓ n).lift (inputForm ℓ n) =
      algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ)) c *
        (aeval (t ℓ n : LaurentSeries (ZMod ℓ)) (A ℓ n) /
          aeval (t ℓ n : LaurentSeries (ZMod ℓ)) (B ℓ n))
  leading_smul : ∀ ℓ n (c : ZMod ℓ) (f : LaurentSeries (ZMod ℓ)),
    leadingValue ℓ n
      (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ)) c * f) =
      c * leadingValue ℓ n f
  class_normalized : ∀ ℓ n [hp : Fact ℓ.Prime],
    leadingValue ℓ n
      (aeval (t ℓ n : LaurentSeries (ZMod ℓ)) (A ℓ n) /
        aeval (t ℓ n : LaurentSeries (ZMod ℓ)) (B ℓ n)) = 1
  lift_normalized : ∀ ℓ n,
    leadingValue ℓ n ((borcherds ℓ n).lift (inputForm ℓ n)) = 1

/-- The output of the theta-cycle, grid-support, and coefficient-duality
argument at one prime and discriminant. -/
def SquareCoefficientSupport (coefficient : ℕ → ℕ → ℤ) (ℓ n : ℕ) : Prop :=
  ∀ m : ℕ, Nat.Coprime m (6 * ℓ) →
    (ℓ : ℤ) ∣ coefficient n m

/-- The paper-internal analytic component: canonicality and admissibility
force the square-coefficient support condition used in the product. -/
def ThetaDualityComponent (coefficient : ℕ → ℕ → ℤ) : Prop :=
  ∀ ℓ n, CanonicalCongruencePrime ℓ → Admissible ℓ n →
    SquareCoefficientSupport coefficient ℓ n

/-- The paper-internal Borcherds/Frobenius bridge, separated from the theta
and duality argument that establishes its premise. -/
def BorcherdsWronskianBridge (coefficient : ℕ → ℕ → ℤ)
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, Admissible ℓ n → SquareCoefficientSupport coefficient ℓ n →
    wronskianObstruction (A ℓ n) (B ℓ n) = 0

/-- The paper-internal volume component: the numerical collision bound
forces the chosen geometric collision predicate to fail. -/
def QuaternionicSeparationComponent
    (collisionFree : ℕ → ℕ → Prop) : Prop :=
  ∀ ℓ n, ℓ.Prime → Admissible ℓ n → (n + 1) ^ 2 < 24 * ℓ →
    collisionFree ℓ n

/-- The integral-coordinate bridge from geometric noncollision to polynomial
coprimality. -/
def CoordinateCoprimalityBridge
    (collisionFree : ℕ → ℕ → Prop)
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, Admissible ℓ n → collisionFree ℓ n →
    IsCoprime (A ℓ n) (B ℓ n)

/-- Monicity of the numerator oriented class polynomial. -/
def NumeratorMonicityComponent
    (A : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, (A ℓ n).Monic

/-- Monicity of the denominator oriented class polynomial. -/
def DenominatorMonicityComponent
    (B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, (B ℓ n).Monic

/-- Degree calculation for the numerator orientations `1` and `11`. -/
def NumeratorDegreeComponent (h : ℕ → ℕ)
    (A : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, (A ℓ n).natDegree = 2 * h n

/-- Degree calculation for the denominator orientations `5` and `7`. -/
def DenominatorDegreeComponent (h : ℕ → ℕ)
    (B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) : Prop :=
  ∀ ℓ n, (B ℓ n).natDegree = 2 * h n

/-- Assemble the degree package from the four independently meaningful class
polynomial conclusions. -/
theorem classPolyDegreeInput_of_components
    (h : ℕ → ℕ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hAm : NumeratorMonicityComponent A)
    (hBm : DenominatorMonicityComponent B)
    (hAd : NumeratorDegreeComponent h A)
    (hBd : DenominatorDegreeComponent h B) :
    ClassPolyDegreeInput h A B := by
  intro ℓ n
  exact ⟨hAm ℓ n, hBm ℓ n, hAd ℓ n, hBd ℓ n⟩

/-- The four conclusions proved by `classPolynomials_arithmetic`, when
available pointwise for the chosen families, directly supply the degree
interface used by the final theorem. -/
theorem classPolyDegreeInput_of_arithmetic
    (h : ℕ → ℕ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (harithmetic : ∀ ℓ n, (A ℓ n).Monic ∧ (B ℓ n).Monic ∧
      (A ℓ n).natDegree = 2 * h n ∧ (B ℓ n).natDegree = 2 * h n) :
    ClassPolyDegreeInput h A B := by
  intro ℓ n
  exact harithmetic ℓ n

/-- The Borcherds bridge follows from its precise substitution premises:
injectivity of `T ↦ t`, nonvanishing of `Θ(t)`, and the chain-rule equation
obtained from the supported Euler product. -/
theorem borcherdsWronskianBridge_of_substitution
    (coefficient : ℕ → ℕ → ℤ)
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (S : ℕ → ℕ → Type*)
    [ringS : ∀ ℓ n, CommRing (S ℓ n)]
    [domainS : ∀ ℓ n, IsDomain (S ℓ n)]
    (substitution : ∀ ℓ n, Polynomial (ZMod ℓ) →+* S ℓ n)
    (hsubstitution : ∀ ℓ n, Function.Injective (substitution ℓ n))
    (thetaT : ∀ ℓ n, S ℓ n)
    (hthetaT : ∀ ℓ n, thetaT ℓ n ≠ 0)
    (hchain : ∀ ℓ n, Admissible ℓ n →
      SquareCoefficientSupport coefficient ℓ n →
      substitution ℓ n (wronskianObstruction (A ℓ n) (B ℓ n)) *
        thetaT ℓ n = 0) :
    BorcherdsWronskianBridge coefficient A B := by
  intro ℓ n hadmissible hsupport
  exact wronskian_zero_of_injective_substitution (A ℓ n) (B ℓ n)
    (substitution ℓ n) (hsubstitution ℓ n) (thetaT ℓ n)
    (hthetaT ℓ n) (hchain ℓ n hadmissible hsupport)

/-- Assemble the obstruction package after passing through the two analytic
components. -/
theorem obstructionInput_of_components
    (coefficient : ℕ → ℕ → ℤ)
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (htheta : ThetaDualityComponent coefficient)
    (hborcherds : BorcherdsWronskianBridge coefficient A B) :
    ObstructionInput A B := by
  intro ℓ n hcanonical hadmissible
  exact hborcherds ℓ n hadmissible (htheta ℓ n hcanonical hadmissible)

/-- Build the obstruction package by invoking the verified infinite-product
coefficient/Frobenius theorem pointwise. -/
theorem obstructionInput_of_infiniteProductData
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (d : InfiniteProductObstructionData A B) :
    ObstructionInput A B := by
  intro ℓ n hcanonical hadmissible
  letI : Fact ℓ.Prime := ⟨hcanonical.prime⟩
  have hinert : legendreSym ℓ (-(n : ℤ)) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using hadmissible.2.2
  have hsquareVanish : ∀ i : ℕ, ¬ℓ ∣ d.index ℓ n i →
      CanonicalCongruencePrime ℓ → Squarefree n → n % 24 = 23 →
      legendreSym ℓ (-(n : ℤ)) = -1 →
        d.H ℓ n ((d.index ℓ n i : ℤ) ^ 2) = 0 := by
    intro i hindex hcan _ _ hinert'
    have hpos : 0 < d.index ℓ n i := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hindex
      simp [hz]
    by_cases hone : d.index ℓ n i = 1
    · rw [hone]
      simpa using
        (Analytic.Hn_first_coefficient_eq_zero_of_canonical_inert
          ℓ n (d.H ℓ n) hcan (d.aK ℓ) (d.euler ℓ) hinert'
          (d.normalization ℓ n))
    · have hgt : 1 < d.index ℓ n i := by omega
      have hgridCycle :=
        Analytic.grid_theta_support_along_chain
          (thetaPowerSeriesLinearMap ℓ ((ℓ - 1) / 2))
          (Analytic.thetaCycleEigenvalue ℓ) (d.grid ℓ n)
          (d.factorChain ℓ n (d.index ℓ n i))
          (d.gridBase ℓ n) (fun m p hm => d.gridStep ℓ n m p hm)
      rw [d.factorChain_prod] at hgridCycle
      exact Analytic.Hn_square_coefficient_eq_zero_of_canonical_inert
        ℓ n (d.index ℓ n i) (d.H ℓ n)
        (d.grid ℓ n (d.index ℓ n i)) (d.chi ℓ n)
        hcan (d.aK ℓ) (d.euler ℓ) hinert' hgt
        (d.normalization ℓ n)
        (d.gridPrincipalPart ℓ n (d.index ℓ n i) hgt)
        (d.weightTwoResidue ℓ n (d.index ℓ n i) hgt)
        hgridCycle
  letI : Zero (d.Scalar ℓ n) := d.scalarZero ℓ n
  have hquotient :
      aeval (d.t ℓ n : LaurentSeries (ZMod ℓ)) (A ℓ n) /
          aeval (d.t ℓ n : LaurentSeries (ZMod ℓ)) (B ℓ n) =
        (d.numerator ℓ n : LaurentSeries (ZMod ℓ)) /
          (d.denominator ℓ n : LaurentSeries (ZMod ℓ)) :=
    normalized_classPolynomial_quotient_product_identity
      (d.borcherds ℓ n) (d.weyl ℓ n)
      (d.borcherdsInput ℓ n) (d.weylInput ℓ n)
      (d.inputForm ℓ n) (d.classDivisor ℓ n)
      (d.t ℓ n : LaurentSeries (ZMod ℓ)) (A ℓ n) (B ℓ n)
      (d.numerator ℓ n : LaurentSeries (ZMod ℓ))
      (d.denominator ℓ n : LaurentSeries (ZMod ℓ))
      (d.leadingValue ℓ n) (d.pairing_zero ℓ n)
      (d.normalization_zero ℓ n) (d.predicted_divisor ℓ n)
      (d.CuspExponentsVanish ℓ n) (d.cusp_of_weyl ℓ n)
      (d.rigidity ℓ n) (d.leading_smul ℓ n)
      (d.class_normalized ℓ n) (d.lift_normalized ℓ n)
      (d.productExpansion_iff ℓ n)
  exact canonicalCongruence_forces_wronskian_zero_from_square_vanishing
    ℓ n (d.index ℓ n) (d.eplus ℓ n) (d.eminus ℓ n)
    (d.numerator ℓ n) (d.denominator ℓ n)
    (d.numeratorProduct ℓ n) (d.denominatorProduct ℓ n)
    (d.H ℓ n) hsquareVanish
    (d.exponentIdentity ℓ n) (d.oneSided ℓ n)
    (d.t ℓ n) (A ℓ n) (B ℓ n)
    (d.tTranscendental ℓ n) (d.thetaT_ne_zero ℓ n)
    (d.classDenominator_ne_zero ℓ n) (d.denominator_ne_zero ℓ n)
    hquotient
    hcanonical hadmissible.1 hadmissible.2.1 hinert

/-- Quaternionic specialization data discharge the volume component when
`collisionFree` is chosen to mean polynomial coprimality. -/
theorem quaternionicSeparationComponent_of_specialization
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hrootSpecialize : ∀ ℓ n {L : Type} [CommRing L] [IsDomain L]
      [Algebra (ZMod ℓ) L] (x : L),
      aeval x (A ℓ n) = 0 → aeval x (B ℓ n) = 0 →
        CollisionSpecializationData ℓ n) :
    QuaternionicSeparationComponent
      (fun ℓ n => IsCoprime (A ℓ n) (B ℓ n)) := by
  intro ℓ n hprime hadmissible hbound
  exact classPolynomial_separation_of_collision_data hprime
    (A ℓ n) (B ℓ n) (hrootSpecialize ℓ n) hbound

/-- With coprimality itself as the collision-free predicate, the coordinate
bridge is the identity implication. -/
theorem coordinateCoprimalityBridge_isCoprime
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ)) :
    CoordinateCoprimalityBridge
      (fun ℓ n => IsCoprime (A ℓ n) (B ℓ n)) A B := by
  intro ℓ n _ hcop
  exact hcop

/-- Hence the separation interface follows directly from the precise CM
specialization premise consumed by `classPolynomial_separation`. -/
theorem separationInput_of_specialization
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (hspecialize : ∀ ℓ n, ℓ.Prime → Admissible ℓ n →
      ¬ IsCoprime (A ℓ n) (B ℓ n) → ∃ m : ℕ,
        n + 1 = 4 * m ∧ 6 * ℓ ≤ 4 * m ^ 2) :
    SeparationInput A B := by
  intro ℓ n hprime hadmissible hbound
  exact classPolynomial_separation (A ℓ n) (B ℓ n)
    (hspecialize ℓ n hprime hadmissible) hbound

/-- Assemble the separation package after the geometric volume step and the
integral-coordinate step have both been supplied. -/
theorem separationInput_of_components
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (collisionFree : ℕ → ℕ → Prop)
    (hvolume : QuaternionicSeparationComponent collisionFree)
    (hcoordinate : CoordinateCoprimalityBridge collisionFree A B) :
    SeparationInput A B := by
  intro ℓ n hprime hadmissible hbound
  exact hcoordinate ℓ n hadmissible
    (hvolume ℓ n hprime hadmissible hbound)

end PaperComponents

open PaperComponents

/-- Paper-faithful conditional classification. Cited results are supplied
through `PaperInterfaces`; the other hypotheses are intermediate outputs of
specific paper sections. -/
theorem paperCanonicalCongruencePrime_iff
    (h : ℕ → ℕ) (coefficient : ℕ → ℕ → ℤ) (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (h5 : PaperInterfaces.Andrews5)
    (h7 : PaperInterfaces.Andrews7)
    (h13 : PaperInterfaces.Andrews13)
    (hfinite : PaperInterfaces.AhlgrenKimFiniteExclusion)
    (hcandidate : SmallInertCandidateInput)
    (hinvariance : PrimeSquareInvarianceInput)
    (hclass : ClassNumberEstimateInput h)
    (hAm : NumeratorMonicityComponent A)
    (hBm : DenominatorMonicityComponent B)
    (hAd : NumeratorDegreeComponent h A)
    (hBd : DenominatorDegreeComponent h B)
    (htheta : ThetaDualityComponent coefficient)
    (hborcherds : BorcherdsWronskianBridge coefficient A B)
    (collisionFree : ℕ → ℕ → Prop)
    (hvolume : QuaternionicSeparationComponent collisionFree)
    (hcoordinate : CoordinateCoprimalityBridge collisionFree A B) :
    ∀ ℓ, CanonicalCongruencePrime ℓ ↔ ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 := by
  have hsmall : SmallDiscriminantInput h :=
    smallDiscriminantInput_of_components h hcandidate hinvariance hclass
  have hdeg : ClassPolyDegreeInput h A B :=
    classPolyDegreeInput_of_components h A B hAm hBm hAd hBd
  have hobs : ObstructionInput A B :=
    obstructionInput_of_components coefficient A B htheta hborcherds
  have hsep : SeparationInput A B :=
    separationInput_of_components A B collisionFree hvolume hcoordinate
  exact canonicalCongruencePrime_iff h A B h5 h7 h13 hfinite
    hsmall hdeg hobs hsep

/-- Paper-facing conditional classification. Its premises include the cited
Andrews, Ahlgren--Kim, and Treviño statements together with structural data
for finite oriented CM families, normalized infinite Borcherds products, and
the specialization collision estimate. The obstruction and separation
conclusions used by the final contradiction are derived in the proof. -/
theorem paperCanonicalCongruencePrime_iff_exact
    (A B : (ℓ n : ℕ) → Polynomial (ZMod ℓ))
    (h5 : PaperInterfaces.Andrews5)
    (h7 : PaperInterfaces.Andrews7)
    (h13 : PaperInterfaces.Andrews13)
    (hfinite : PaperInterfaces.AhlgrenKimFiniteExclusion)
    (Nonprincipal : ℕ → (ℤ → ℤ) → Prop)
    (hTrevino : PaperInterfaces.TrevinoCorrectedCharacterBound Nonprincipal)
    (hnonprincipal :
      ∀ (p : ℕ) [Fact p.Prime], Nonprincipal p (legendreSym p))
    (I1 I11 I5 I7 : ℕ → ℕ → Type*)
    [fI1 : ∀ ℓ n, Fintype (I1 ℓ n)]
    [fI11 : ∀ ℓ n, Fintype (I11 ℓ n)]
    [fI5 : ∀ ℓ n, Fintype (I5 ℓ n)]
    [fI7 : ∀ ℓ n, Fintype (I7 ℓ n)]
    (t1 : ∀ ℓ n, I1 ℓ n → ZMod ℓ)
    (t11 : ∀ ℓ n, I11 ℓ n → ZMod ℓ)
    (t5 : ∀ ℓ n, I5 ℓ n → ZMod ℓ)
    (t7 : ∀ ℓ n, I7 ℓ n → ZMod ℓ)
    (hA : ∀ ℓ n, A ℓ n = classPolyA (t1 ℓ n) (t11 ℓ n))
    (hB : ∀ ℓ n, B ℓ n = classPolyB (t5 ℓ n) (t7 ℓ n))
    (hcard1 : ∀ ℓ n, Fintype.card (I1 ℓ n) = negativeClassNumber n)
    (hcard11 : ∀ ℓ n, Fintype.card (I11 ℓ n) = negativeClassNumber n)
    (hcard5 : ∀ ℓ n, Fintype.card (I5 ℓ n) = negativeClassNumber n)
    (hcard7 : ∀ ℓ n, Fintype.card (I7 ℓ n) = negativeClassNumber n)
    (hproduct : InfiniteProductObstructionData A B)
    (hrootSpecialize : ∀ ℓ n {L : Type} [CommRing L] [IsDomain L]
      [Algebra (ZMod ℓ) L] (x : L),
      aeval x (A ℓ n) = 0 → aeval x (B ℓ n) = 0 →
        CollisionSpecializationData ℓ n) :
    ∀ ℓ, CanonicalCongruencePrime ℓ ↔ ℓ = 5 ∨ ℓ = 7 ∨ ℓ = 13 := by
  have hclass : ClassNumberEstimateInput negativeClassNumber := by
    intro n _ hsquarefree hmod
    exact ⟨negativeClassNumber_pos hmod,
      class_number_bound hsquarefree hmod⟩
  have hsmall : SmallDiscriminantInput negativeClassNumber :=
    smallDiscriminantInput_of_components negativeClassNumber
      (smallInertCandidateInput_of_trevino
        Nonprincipal hTrevino hnonprincipal)
      primeSquareInvarianceInput hclass
  have hobs : ObstructionInput A B :=
    obstructionInput_of_infiniteProductData A B hproduct
  intro ℓ
  constructor
  · intro hcanonical
    have hprime := hcanonical.prime
    by_cases hbelow : ℓ < cutoff
    · exact hfinite ℓ hcanonical hbelow
    · have hlarge : cutoff ≤ ℓ := Nat.le_of_not_gt hbelow
      obtain ⟨n, hadmissible, hcollision, hdegree_pos, hdegree_lt⟩ :=
        hsmall ℓ hprime hlarge
      letI : Fact ℓ.Prime := ⟨hprime⟩
      have harithmetic :=
        classPolynomials_arithmetic
          (t1 ℓ n) (t11 ℓ n) (t5 ℓ n) (t7 ℓ n)
          (negativeClassNumber n)
          (hcard1 ℓ n) (hcard11 ℓ n) (hcard5 ℓ n) (hcard7 ℓ n)
      have hmonic : (A ℓ n).Monic := by
        rw [hA ℓ n]
        exact harithmetic.1
      have hdegree : (A ℓ n).natDegree =
          2 * negativeClassNumber n := by
        rw [hA ℓ n]
        exact harithmetic.2.2.1
      have hcop : IsCoprime (A ℓ n) (B ℓ n) :=
        classPolynomial_separation_of_collision_data hprime
          (A ℓ n) (B ℓ n) (hrootSpecialize ℓ n) hcollision
      have hnonzero : wronskianObstruction (A ℓ n) (B ℓ n) ≠ 0 :=
        wronskianObstruction_ne_zero_zmod hprime hcop hmonic
          (hdegree ▸ hdegree_pos) (hdegree ▸ hdegree_lt)
      exact (hnonzero (hobs ℓ n hcanonical hadmissible)).elim
  · rintro (rfl | rfl | rfl)
    · exact h5
    · exact h7
    · exact h13

end SptCM
