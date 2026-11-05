module

public import blessed.SptCM.Repair.CMPolynomialReduction
public import blessed.SptCM.Quaternion.Separation
public import blessed.SptCM.Literature.RolenLiterature
public import blessed.SptCM.CM.Repaired.ActualCMValues
public import Mathlib.Tactic

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# Repairs I18--I20: geometric collision and quaternionic separation

This file factors the CM part of the argument into three steps.  A corrected
common root (in an algebraic closure, rather than necessarily in the prime
field) is sent to two CM points.  The general E8 theorems then supply good
reduction, supersingularity and injectivity.  The orientation calculation
proves that the two specialized actions do not commute, and the general E9
Hadamard theorem gives the numerical volume bound.

The structures below contain only the concrete specialization maps and the
normalization computations needed to instantiate E8 and E9.  In particular,
none has a coprimality or separation field.
-/

namespace SptCM.Repair

noncomputable section

open Polynomial
open SptCM.RolenLiterature

universe u

/-- The paper-specific map from a geometric collision to its two CM points.
The equality of reductions is the content of the integral-coordinate
specialization; inertness is the elementary discriminant calculation. -/
structure RootToCMData
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) where
  points : HasGeometricCMCollision P h6 → CMPoint × CMPoint
  sameReduction : ∀ h,
    CM.reduction (points h).1 = CM.reduction (points h).2
  numeratorInert : ∀ h, CM.inertAt ℓ (points h).1
  denominatorInert : ∀ h, CM.inertAt ℓ (points h).2

/-- The output of I18.  All theorem-valued fields here are derived from E8;
this record is an output, not an input interface. -/
structure GeometricCMSpecialization
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism) where
  numeratorPoint : CMPoint
  denominatorPoint : CMPoint
  sameReduction :
    CM.reduction numeratorPoint = CM.reduction denominatorPoint
  numeratorGoodReduction : CM.hasPotentiallyGoodReduction numeratorPoint
  denominatorGoodReduction : CM.hasPotentiallyGoodReduction denominatorPoint
  supersingular : CM.supersingular (CM.reduction numeratorPoint)
  numeratorActionInjective : CM.specializationInjective numeratorPoint
  denominatorActionInjective : CM.specializationInjective denominatorPoint

/-- I18: a common geometric root specializes to one supersingular reduction
carrying the two injectively specialized CM actions. -/
@[expose]
def common_root_specialization
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism)
    (hE8 : E8StandardCM CM) (D : RootToCMData P h6 CM)
    (hcollision : HasGeometricCMCollision P h6) :
    GeometricCMSpecialization CM :=
  { numeratorPoint := (D.points hcollision).1
    denominatorPoint := (D.points hcollision).2
    sameReduction := D.sameReduction hcollision
    numeratorGoodReduction := hE8.2.1 _
    denominatorGoodReduction := hE8.2.1 _
    supersingular := hE8.2.2.1 ℓ _ (D.numeratorInert hcollision)
    numeratorActionInjective := hE8.2.2.2 _
    denominatorActionInjective := hE8.2.2.2 _ }

/-- The proposition-valued form of `common_root_specialization`: once the
paper-specific root-to-CM map has been constructed, the permitted E8 results
produce the complete specialized pair. -/
theorem common_root_specialization_exists
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {Order IdealClass CMPoint Reduction Endomorphism : Type*}
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction Endomorphism)
    (hE8 : E8StandardCM CM) (D : RootToCMData P h6 CM)
    (hcollision : HasGeometricCMCollision P h6) :
    Nonempty (GeometricCMSpecialization CM) :=
  ⟨common_root_specialization P h6 CM hE8 D hcollision⟩

/-- The scalar by which
`\omega = a\tau_Q + (b+1)/2` acts on the standard cyclic subgroup
`C_Q = ⟨1/6⟩`.  Only the residue of `b` modulo `12` matters. -/
@[expose]
def orientationScalar (b : ℕ) : ZMod 6 := ((b + 1) / 2 : ℕ)

/-! ### The actual quadratic element before specialization -/

/-- For a raw form `Q = [a,b,c]`, the element
`a τ_Q + (b+1)/2` in the corresponding complex quadratic order. -/
@[expose]
noncomputable def rawOmega {n r : ℕ} (Q : SptCM.RawOrientedForm n r) : ℂ :=
  (Q.1.a : ℂ) * SptCM.CM.Repaired.rawCMPoint Q +
    ((Q.1.b : ℂ) + 1) / 2

/-- Direct substitution of the canonical CM point shows that `rawOmega` is
the fixed quadratic element `(1 + √(-n))/2`, independently of the chosen
oriented form. -/
theorem rawOmega_eq {n r : ℕ} (Q : SptCM.RawOrientedForm n r) :
    rawOmega Q = (1 + Complex.I * Real.sqrt n) / 2 := by
  have ha : (Q.1.a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Q.2.2.1)
  unfold rawOmega SptCM.CM.Repaired.rawCMPoint
  field_simp
  ring

/-- Complex conjugation sends the actual quadratic element to `1-ω`. -/
theorem star_rawOmega {n r : ℕ} (Q : SptCM.RawOrientedForm n r) :
    star (rawOmega Q) = 1 - rawOmega Q := by
  rw [rawOmega_eq]
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring

/-- The reduced trace of the actual quadratic element is one. -/
theorem reducedTrace_rawOmega {n r : ℕ} (Q : SptCM.RawOrientedForm n r) :
    SptCM.reducedTrace (rawOmega Q) = 1 := by
  rw [SptCM.reducedTrace, star_rawOmega]
  ring

/-- Its reduced norm is `(n+1)/4`. -/
theorem reducedNorm_rawOmega {n r : ℕ} (hn : 0 < n)
    (Q : SptCM.RawOrientedForm n r) :
    SptCM.reducedNorm (rawOmega Q) = ((n : ℂ) + 1) / 4 := by
  rw [SptCM.reducedNorm, star_rawOmega, rawOmega_eq]
  have hsqrt : (Real.sqrt n) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  apply Complex.ext
  · simp [Complex.div_re, Complex.div_im]
    nlinarith [hsqrt]
  · simp [Complex.div_re, Complex.div_im]
    ring

/-- Equivalently, `ω` satisfies its quadratic polynomial
`X²-X+(n+1)/4`. -/
theorem rawOmega_quadratic_relation {n r : ℕ} (hn : 0 < n)
    (Q : SptCM.RawOrientedForm n r) :
    rawOmega Q ^ 2 - rawOmega Q + ((n : ℂ) + 1) / 4 = 0 := by
  have hnorm := reducedNorm_rawOmega hn Q
  rw [SptCM.reducedNorm, star_rawOmega] at hnorm
  rw [← hnorm]
  ring

/-! ### The same calculation in the canonical quadratic order -/

/-- The distinguished generator of the concrete order
`ℤ[X]/(X²-X+(n+1)/4)` used by the E8 interface. -/
@[expose]
noncomputable def negativeQuadraticOmega (n : ℕ) :
    NegativeQuadraticOrder n :=
  AdjoinRoot.root _

/-- The distinguished generator satisfies the defining integral quadratic
equation.  This is the algebraic identity that a genuine specialization
homomorphism must transport; no trace or norm formula is assumed here. -/
theorem negativeQuadraticOmega_quadratic_relation (n : ℕ) :
    negativeQuadraticOmega n ^ 2 - negativeQuadraticOmega n +
        AdjoinRoot.of
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
          (((n + 1) / 4 : ℕ) : ℤ) = 0 := by
  let f : ℤ[X] :=
    Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((n + 1) / 4 : ℕ) : ℤ)
  have h := AdjoinRoot.eval₂_root f
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  simpa [f, negativeQuadraticOmega] using h

/-- Every ring specialization of the canonical quadratic order transports
the defining equation of its generator. -/
theorem map_negativeQuadraticOmega_quadratic_relation
    {n : ℕ} {D : Type*} [Ring D]
    (φ : NegativeQuadraticOrder n →+* D) :
    φ (negativeQuadraticOmega n) ^ 2 - φ (negativeQuadraticOmega n) +
        φ (AdjoinRoot.of
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
          (((n + 1) / 4 : ℕ) : ℤ)) = 0 := by
  simpa only [map_sub, map_add, map_pow, map_zero] using
    congrArg φ (negativeQuadraticOmega_quadratic_relation n)

/-- A specialization which respects conjugation has trace one on the
canonical generator. -/
theorem reducedTrace_map_negativeQuadraticOmega
    {n : ℕ} {D : Type*} [Ring D] [Star D]
    (φ : NegativeQuadraticOrder n →+* D)
    (hstar : star (φ (negativeQuadraticOmega n)) =
      1 - φ (negativeQuadraticOmega n)) :
    SptCM.reducedTrace (φ (negativeQuadraticOmega n)) = 1 := by
  rw [SptCM.reducedTrace, hstar]
  noncomm_ring

/-- The norm formula for a specialized canonical generator is derived from
its transported quadratic equation and conjugation compatibility. -/
theorem reducedNorm_map_negativeQuadraticOmega
    {n : ℕ} {D : Type*} [Ring D] [Star D]
    (φ : NegativeQuadraticOrder n →+* D)
    (hstar : star (φ (negativeQuadraticOmega n)) =
      1 - φ (negativeQuadraticOmega n)) :
    SptCM.reducedNorm (φ (negativeQuadraticOmega n)) =
      φ (AdjoinRoot.of
        (Polynomial.X ^ 2 - Polynomial.X +
          Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
        (((n + 1) / 4 : ℕ) : ℤ)) := by
  have hrel := map_negativeQuadraticOmega_quadratic_relation φ
  rw [SptCM.reducedNorm, hstar]
  have hneg :
      φ (negativeQuadraticOmega n) ^ 2 -
          φ (negativeQuadraticOmega n) =
        -φ (AdjoinRoot.of
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
          (((n + 1) / 4 : ℕ) : ℤ)) :=
    eq_neg_of_add_eq_zero_left hrel
  calc
    φ (negativeQuadraticOmega n) *
        (1 - φ (negativeQuadraticOmega n)) =
        -(φ (negativeQuadraticOmega n) ^ 2 -
          φ (negativeQuadraticOmega n)) := by noncomm_ring
    _ = -(-φ (AdjoinRoot.of
          (Polynomial.X ^ 2 - Polynomial.X +
            Polynomial.C (((n + 1) / 4 : ℕ) : ℤ))
          (((n + 1) / 4 : ℕ) : ℤ))) := congrArg Neg.neg hneg
    _ = _ := neg_neg _

/-- In any target ring the norm is the canonical integer `(n+1)/4`, rather
than a value depending on the chosen specialization homomorphism. -/
theorem reducedNorm_map_negativeQuadraticOmega_eq_natCast
    {n : ℕ} {D : Type*} [Ring D] [Star D]
    (φ : NegativeQuadraticOrder n →+* D)
    (hstar : star (φ (negativeQuadraticOmega n)) =
      1 - φ (negativeQuadraticOmega n)) :
    SptCM.reducedNorm (φ (negativeQuadraticOmega n)) =
      (((n + 1) / 4 : ℕ) : D) := by
  rw [reducedNorm_map_negativeQuadraticOmega φ hstar]
  rw [← AdjoinRoot.algebraMap_eq]
  rw [RingHom.eq_intCast' (algebraMap ℤ (NegativeQuadraticOrder n))]
  change φ (((((n + 1) / 4 : ℕ) : ℤ)) :
    NegativeQuadraticOrder n) = _
  rw [map_intCast]
  change ((((n : ℤ) + 1) / 4 : ℤ) : D) =
    (((n + 1) / 4 : ℕ) : D)
  have hz : ((n : ℤ) + 1) / 4 =
      (((n + 1) / 4 : ℕ) : ℤ) := by
    simpa using (Int.natCast_div (n + 1) 4).symm
  calc
    ((((n : ℤ) + 1) / 4 : ℤ) : D) =
        (((((n + 1) / 4 : ℕ) : ℤ)) : D) :=
      congrArg (fun z : ℤ => (z : D)) hz
    _ = (((n + 1) / 4 : ℕ) : D) :=
      Int.cast_natCast ((n + 1) / 4)

/-- Any two conjugation-compatible specializations of the same canonical
quadratic order have equal reduced norm. -/
theorem reducedNorm_maps_negativeQuadraticOmega_eq
    {n : ℕ} {D : Type*} [Ring D] [Star D]
    (φ ψ : NegativeQuadraticOrder n →+* D)
    (hstarφ : star (φ (negativeQuadraticOmega n)) =
      1 - φ (negativeQuadraticOmega n))
    (hstarψ : star (ψ (negativeQuadraticOmega n)) =
      1 - ψ (negativeQuadraticOmega n)) :
    SptCM.reducedNorm (φ (negativeQuadraticOmega n)) =
      SptCM.reducedNorm (ψ (negativeQuadraticOmega n)) := by
  rw [reducedNorm_map_negativeQuadraticOmega_eq_natCast φ hstarφ,
    reducedNorm_map_negativeQuadraticOmega_eq_natCast ψ hstarψ]

@[simp] theorem orientationScalar_one : orientationScalar 1 = 1 := by
  norm_num [orientationScalar]

@[simp] theorem orientationScalar_eleven : orientationScalar 11 = 0 := by
  change (6 : ZMod 6) = 0
  exact ZMod.natCast_self 6

@[simp] theorem orientationScalar_five : orientationScalar 5 = 3 := by
  norm_num [orientationScalar]

@[simp] theorem orientationScalar_seven : orientationScalar 7 = 4 := by
  norm_num [orientationScalar]

/-- Concrete orientation and characteristic-polynomial data for the two
specialized CM actions.  The trace-one and common-norm fields are calculations
about the constructed CM elements, not an assumed centralizer,
noncommutation, or separation conclusion. -/
structure OrientedSpecializedActions
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM) where
  levelOrder : Subring D
  levelAction : levelOrder →+* ZMod 6
  numeratorPreservesLevel :
    CM.specializedAction S.numeratorPoint ∈ levelOrder
  denominatorPreservesLevel :
    CM.specializedAction S.denominatorPoint ∈ levelOrder
  numeratorResidue : ℕ
  denominatorResidue : ℕ
  numeratorOrientation : numeratorResidue = 1 ∨ numeratorResidue = 11
  denominatorOrientation : denominatorResidue = 5 ∨ denominatorResidue = 7
  numeratorScalarFormula :
    levelAction ⟨CM.specializedAction S.numeratorPoint,
      numeratorPreservesLevel⟩ =
      orientationScalar numeratorResidue
  denominatorScalarFormula :
    levelAction ⟨CM.specializedAction S.denominatorPoint,
      denominatorPreservesLevel⟩ =
      orientationScalar denominatorResidue
  numeratorTraceOne :
    SptCM.reducedTrace (CM.specializedAction S.numeratorPoint) = 1
  denominatorTraceOne :
    SptCM.reducedTrace (CM.specializedAction S.denominatorPoint) = 1
  commonReducedNorm :
    SptCM.reducedNorm (CM.specializedAction S.numeratorPoint) =
      SptCM.reducedNorm (CM.specializedAction S.denominatorPoint)

/-- Construct the action specification from genuine quadratic-order
specialization homomorphisms.  In particular, the trace and common-norm
fields are proved from the defining equation of the order generator and are
not hypotheses of this constructor.  The remaining scalar formulas are
exactly the still-geometric compatibility with the cyclic level subgroup. -/
@[expose]
def OrientedSpecializedActions.ofQuadraticSpecializations
    {n : ℕ}
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (levelOrder : Subring D)
    (levelAction : levelOrder →+* ZMod 6)
    (numeratorResidue denominatorResidue : ℕ)
    (numeratorOrientation :
      numeratorResidue = 1 ∨ numeratorResidue = 11)
    (denominatorOrientation :
      denominatorResidue = 5 ∨ denominatorResidue = 7)
    (numeratorMap denominatorMap : NegativeQuadraticOrder n →+* D)
    (numeratorAction :
      CM.specializedAction S.numeratorPoint =
        numeratorMap (negativeQuadraticOmega n))
    (denominatorAction :
      CM.specializedAction S.denominatorPoint =
        denominatorMap (negativeQuadraticOmega n))
    (numeratorPreservesLevel :
      CM.specializedAction S.numeratorPoint ∈ levelOrder)
    (denominatorPreservesLevel :
      CM.specializedAction S.denominatorPoint ∈ levelOrder)
    (numeratorStar :
      star (numeratorMap (negativeQuadraticOmega n)) =
        1 - numeratorMap (negativeQuadraticOmega n))
    (denominatorStar :
      star (denominatorMap (negativeQuadraticOmega n)) =
        1 - denominatorMap (negativeQuadraticOmega n))
    (numeratorScalarFormula :
      levelAction ⟨CM.specializedAction S.numeratorPoint,
        numeratorPreservesLevel⟩ =
        orientationScalar numeratorResidue)
    (denominatorScalarFormula :
      levelAction ⟨CM.specializedAction S.denominatorPoint,
        denominatorPreservesLevel⟩ =
        orientationScalar denominatorResidue) :
    OrientedSpecializedActions CM S where
  levelOrder := levelOrder
  levelAction := levelAction
  numeratorPreservesLevel := numeratorPreservesLevel
  denominatorPreservesLevel := denominatorPreservesLevel
  numeratorResidue := numeratorResidue
  denominatorResidue := denominatorResidue
  numeratorOrientation := numeratorOrientation
  denominatorOrientation := denominatorOrientation
  numeratorScalarFormula := numeratorScalarFormula
  denominatorScalarFormula := denominatorScalarFormula
  numeratorTraceOne := by
    rw [numeratorAction]
    exact reducedTrace_map_negativeQuadraticOmega numeratorMap numeratorStar
  denominatorTraceOne := by
    rw [denominatorAction]
    exact reducedTrace_map_negativeQuadraticOmega denominatorMap denominatorStar
  commonReducedNorm := by
    rw [numeratorAction, denominatorAction]
    exact reducedNorm_maps_negativeQuadraticOmega_eq numeratorMap denominatorMap
      numeratorStar denominatorStar

/-- The paper-specific geometric identification left after E8: the two CM
points obtained from a collision are represented by actual raw oriented forms
in the numerator and denominator residue families.  It stores no trace, norm,
scalar-action, noncommutation, or volume conclusion. -/
structure CollisionOrientedFormData
    {n : ℕ}
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (E8Q : E8OrientedQuadraticSpecialization n CM) where
  numeratorResidue : ℕ
  denominatorResidue : ℕ
  numeratorOrientation : numeratorResidue = 1 ∨ numeratorResidue = 11
  denominatorOrientation : denominatorResidue = 5 ∨ denominatorResidue = 7
  numeratorForm : SptCM.RawOrientedForm n numeratorResidue
  denominatorForm : SptCM.RawOrientedForm n denominatorResidue
  numeratorPoint :
    S.numeratorPoint = E8Q.point numeratorResidue numeratorForm
  denominatorPoint :
    S.denominatorPoint = E8Q.point denominatorResidue denominatorForm

/-- I19, with the genuine E8 specialization boundary: once the collision
points are identified with their two raw oriented forms, the general E8
ring-specialization and level-action laws construct the complete action
specification.  Trace one and common norm are internal consequences. -/
@[expose]
def actualOrientedSpecializedActions_of_E8
    {n : ℕ}
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (F : CollisionOrientedFormData CM S E8Q) :
    OrientedSpecializedActions CM S :=
  OrientedSpecializedActions.ofQuadraticSpecializations CM S
    E8Q.levelOrder E8Q.levelAction
    F.numeratorResidue F.denominatorResidue
    F.numeratorOrientation F.denominatorOrientation
    (E8Q.specialize F.numeratorForm)
    (E8Q.specialize F.denominatorForm)
    (by
      rw [F.numeratorPoint]
      exact E8Q.specializedGenerator F.numeratorForm)
    (by
      rw [F.denominatorPoint]
      exact E8Q.specializedGenerator F.denominatorForm)
    (by
      rw [F.numeratorPoint]
      exact E8Q.specializedGenerator_mem_levelOrder F.numeratorForm)
    (by
      rw [F.denominatorPoint]
      exact E8Q.specializedGenerator_mem_levelOrder F.denominatorForm)
    (E8Q.conjugationGenerator F.numeratorForm)
    (E8Q.conjugationGenerator F.denominatorForm)
    (by
      have hsub :
          (⟨CM.specializedAction S.numeratorPoint, by
              rw [F.numeratorPoint]
              exact E8Q.specializedGenerator_mem_levelOrder
                F.numeratorForm⟩ : E8Q.levelOrder) =
            ⟨CM.specializedAction
                (E8Q.point F.numeratorResidue F.numeratorForm),
              E8Q.specializedGenerator_mem_levelOrder F.numeratorForm⟩ := by
        apply Subtype.ext
        exact congrArg CM.specializedAction F.numeratorPoint
      rw [hsub]
      exact E8Q.levelAction_specializedGenerator F.numeratorForm)
    (by
      have hsub :
          (⟨CM.specializedAction S.denominatorPoint, by
              rw [F.denominatorPoint]
              exact E8Q.specializedGenerator_mem_levelOrder
                F.denominatorForm⟩ : E8Q.levelOrder) =
            ⟨CM.specializedAction
                (E8Q.point F.denominatorResidue F.denominatorForm),
              E8Q.specializedGenerator_mem_levelOrder F.denominatorForm⟩ := by
        apply Subtype.ext
        exact congrArg CM.specializedAction F.denominatorPoint
      rw [hsub]
      exact E8Q.levelAction_specializedGenerator F.denominatorForm)

/-- The numerator orientations `b ≡ 1,11 (mod 12)` give exactly the
two scalars `1,0` on the level-six subgroup. -/
theorem OrientedSpecializedActions.numeratorScalar
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (A : OrientedSpecializedActions CM S) :
    A.levelAction ⟨CM.specializedAction S.numeratorPoint,
      A.numeratorPreservesLevel⟩ = 0 ∨
      A.levelAction ⟨CM.specializedAction S.numeratorPoint,
        A.numeratorPreservesLevel⟩ = 1 := by
  rcases A.numeratorOrientation with h | h
  · right
    simpa [h] using A.numeratorScalarFormula
  · left
    simpa [h] using A.numeratorScalarFormula

/-- The denominator orientations `b ≡ 5,7 (mod 12)` give exactly the
two scalars `3,4` on the level-six subgroup. -/
theorem OrientedSpecializedActions.denominatorScalar
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (A : OrientedSpecializedActions CM S) :
    A.levelAction ⟨CM.specializedAction S.denominatorPoint,
      A.denominatorPreservesLevel⟩ = 3 ∨
      A.levelAction ⟨CM.specializedAction S.denominatorPoint,
        A.denominatorPreservesLevel⟩ = 4 := by
  rcases A.denominatorOrientation with h | h
  · left
    simpa [h] using A.denominatorScalarFormula
  · right
    simpa [h] using A.denominatorScalarFormula

/-- In a division ring, two commuting elements of reduced trace one and equal
reduced norm are the two roots of the same quadratic polynomial.  Thus they
are equal or exchanged by quaternionic conjugation.  No classification of a
centralizer is needed beyond the fact that the two elements commute. -/
theorem centralizer_alternative_of_trace_one_norm_eq
    {D : Type*} [DivisionRing D] [Star D] (α β : D)
    (htraceAlpha : SptCM.reducedTrace α = 1)
    (htraceBeta : SptCM.reducedTrace β = 1)
    (hnorm : SptCM.reducedNorm α = SptCM.reducedNorm β)
    (hcomm : Commute α β) :
    β = α ∨ β = 1 - α := by
  have hstarAlpha : star α = 1 - α := by
    rw [SptCM.reducedTrace] at htraceAlpha
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using htraceAlpha)
  have hstarBeta : star β = 1 - β := by
    rw [SptCM.reducedTrace] at htraceBeta
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using htraceBeta)
  rw [SptCM.reducedNorm, hstarAlpha, SptCM.reducedNorm, hstarBeta] at hnorm
  have hfactor : (β - α) * (β + α - 1) = 0 := by
    calc
      (β - α) * (β + α - 1) =
          α * (1 - α) - β * (1 - β) := by
            noncomm_ring [hcomm.eq]
      _ = 0 := sub_eq_zero.mpr hnorm
  rcases mul_eq_zero.mp hfactor with hsame | hcomplement
  · exact Or.inl (sub_eq_zero.mp hsame)
  · right
    exact eq_sub_of_add_eq (sub_eq_zero.mp hcomplement)

/-- I19: the disjoint orientation scalars and the quadratic trace/norm
calculation force the two specialized actions not to commute. -/
theorem specialized_actions_noncommute
    {Order IdealClass CMPoint Reduction D : Type*}
    [DivisionRing D] [Star D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (A : OrientedSpecializedActions CM S) :
    ¬ Commute (CM.specializedAction S.numeratorPoint)
        (CM.specializedAction S.denominatorPoint) := by
  exact SptCM.orientation_actions_noncommute_of_preserving_subring A.levelOrder
    (CM.specializedAction S.numeratorPoint)
    (CM.specializedAction S.denominatorPoint)
    A.numeratorPreservesLevel A.denominatorPreservesLevel A.levelAction
    (A.numeratorScalar CM S) (A.denominatorScalar CM S)
    (fun hcomm => centralizer_alternative_of_trace_one_norm_eq _ _
      A.numeratorTraceOne A.denominatorTraceOne A.commonReducedNorm hcomm)

/-- Hence, in a central division algebra, the four elements used in the
Goren--Lauter lattice are linearly independent. -/
theorem specialized_actions_linearIndependent
    {F Order IdealClass CMPoint Reduction D : Type*}
    [Field F] [DivisionRing D] [Star D] [Algebra F D]
    (CM : CMTheoryModel Order IdealClass CMPoint Reduction D)
    (S : GeometricCMSpecialization CM)
    (A : OrientedSpecializedActions CM S) :
    LinearIndependent F
      ![(1 : D), CM.specializedAction S.numeratorPoint,
        CM.specializedAction S.denominatorPoint,
        CM.specializedAction S.numeratorPoint *
          CM.specializedAction S.denominatorPoint] := by
  exact SptCM.noncommuting_lattice_linearIndependent _ _
    (specialized_actions_noncommute CM S A)

/-- The concrete normalization facts needed to read E9's abstract covolume
bound numerically.  `covolumeLower` is the local index computation after
Arpin identifies the preserving order; the four norm equalities are the
standard reduced-norm calculation.  No field states the desired volume bound. -/
structure LevelSixCovolumeNormalization
    (ℓ m : ℕ)
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Algebra ℚ D]
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D)
    (E : Curve) (C : Subgroup) (α β : D) where
  cyclic : EC.cyclicOfOrderSix C
  independentOfLinearIndependent :
    LinearIndependent ℚ ![(1 : D), α, β, α * β] →
      EC.independent (1 : D) α β (α * β)
  covolumeNonnegative :
    0 ≤ EC.covolume (EC.span (1 : D) α β (α * β))
  covolumeLower :
    EC.isEichlerOfLevelSix (EC.preservingOrder E C) →
      (6 * ℓ : ℝ) ≤ EC.covolume (EC.span (1 : D) α β (α * β))
  normOne : EC.squaredNorm (1 : D) = 2
  normAlpha : EC.squaredNorm α = 2 * m
  normBeta : EC.squaredNorm β = 2 * m
  normProduct : EC.squaredNorm (α * β) = 2 * m ^ 2

/-- I20: Arpin's order identification and the Goren--Lauter inequality,
together with the explicit local-index and reduced-norm normalizations, give
`6ℓ ≤ 4m²`. -/
theorem levelSix_covolume_inequality_of_E9
    {ℓ m : ℕ}
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Algebra ℚ D]
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D)
    (hE9 : E9ArpinGorenLauter EC)
    (E : Curve) (C : Subgroup) (α β : D)
    (hss : EC.supersingular E)
    (hnoncomm : ¬ Commute α β)
    (N : LevelSixCovolumeNormalization ℓ m EC E C α β) :
    6 * ℓ ≤ 4 * m ^ 2 := by
  have hEichler : EC.isEichlerOfLevelSix (EC.preservingOrder E C) :=
    hE9.1 E C hss N.cyclic
  have hLI : LinearIndependent ℚ ![(1 : D), α, β, α * β] :=
    SptCM.noncommuting_lattice_linearIndependent α β hnoncomm
  have hHadamard := hE9.2 (1 : D) α β (α * β)
    (N.independentOfLinearIndependent hLI)
  rw [N.normOne, N.normAlpha, N.normBeta, N.normProduct] at hHadamard
  have hlower := N.covolumeLower hEichler
  have hreal : (6 * ℓ : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by
    have hm : (0 : ℝ) ≤ m := by positivity
    nlinarith [N.covolumeNonnegative]
  exact_mod_cast hreal

/-- A common collision also determines the natural number which is the common
reduced norm.  This is kept separate from the specialization and quaternionic
literature interfaces so that it cannot hide separation. -/
structure CommonNormData (n : ℕ) where
  norm : ℕ
  normIdentity : n + 1 = 4 * norm

/-- Generic I18--I20 composition.  Every corrected geometric collision gives
an E8 specialization; its explicitly computed actions are noncommuting; E9
then yields the volume inequality. -/
theorem common_root_specialization_to_volume
    {n ℓ : ℕ} (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {OrderCM IdealClass CMPoint Curve D Subgroup OrderEC Lattice : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (CM : CMTheoryModel OrderCM IdealClass CMPoint Curve D)
    (EC : EichlerCovolumeModel Curve Subgroup OrderEC Lattice D)
    (supersingularCompatible : ∀ E, CM.supersingular E → EC.supersingular E)
    (hE8 : E8StandardCM CM) (hE9 : E9ArpinGorenLauter EC)
    (rootData : RootToCMData P h6 CM)
    (collisionCurve : ∀ h : HasGeometricCMCollision P h6,
      Curve)
    (curveEq : ∀ h,
      collisionCurve h = CM.reduction (rootData.points h).1)
    (levelSubgroup : ∀ h : HasGeometricCMCollision P h6, Subgroup)
    (actionData : ∀ h : HasGeometricCMCollision P h6,
      OrientedSpecializedActions CM
        (common_root_specialization P h6 CM hE8 rootData h))
    (normData : HasGeometricCMCollision P h6 → CommonNormData n)
    (normalization : ∀ h : HasGeometricCMCollision P h6,
      LevelSixCovolumeNormalization ℓ (normData h).norm EC
        (collisionCurve h) (levelSubgroup h)
        (CM.specializedAction
          (common_root_specialization P h6 CM hE8 rootData h).numeratorPoint)
        (CM.specializedAction
          (common_root_specialization P h6 CM hE8 rootData h).denominatorPoint))
    (hcollision : HasGeometricCMCollision P h6) :
    ∃ m : ℕ, n + 1 = 4 * m ∧ 6 * ℓ ≤ 4 * m ^ 2 := by
  let S := common_root_specialization P h6 CM hE8 rootData hcollision
  let A := actionData hcollision
  let N := normalization hcollision
  refine ⟨(normData hcollision).norm, (normData hcollision).normIdentity, ?_⟩
  apply levelSix_covolume_inequality_of_E9 EC hE9
    (collisionCurve hcollision) (levelSubgroup hcollision)
    (CM.specializedAction S.numeratorPoint)
    (CM.specializedAction S.denominatorPoint)
  · rw [curveEq hcollision]
    apply supersingularCompatible
    simpa [S, common_root_specialization] using S.supersingular
  · exact specialized_actions_noncommute CM S A
  · exact N

/-- Generic separation theorem obtained from I18--I20.  It assumes only the
strict numerical collision bound in addition to the concrete construction
and the general E8/E9 literature theorems; coprimality is the conclusion. -/
theorem classPolynomial_separation_of_E8_E9
    {n ℓ : ℕ} (hprime : ℓ.Prime)
    (P : SptCM.IntegralOrientedClassPolynomials n)
    (h6 : IsUnit (6 : ZMod ℓ))
    {OrderCM IdealClass CMPoint Curve D Subgroup OrderEC Lattice : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (CM : CMTheoryModel OrderCM IdealClass CMPoint Curve D)
    (EC : EichlerCovolumeModel Curve Subgroup OrderEC Lattice D)
    (supersingularCompatible : ∀ E, CM.supersingular E → EC.supersingular E)
    (hE8 : E8StandardCM CM) (hE9 : E9ArpinGorenLauter EC)
    (rootData : RootToCMData P h6 CM)
    (collisionCurve : ∀ h : HasGeometricCMCollision P h6, Curve)
    (curveEq : ∀ h,
      collisionCurve h = CM.reduction (rootData.points h).1)
    (levelSubgroup : ∀ h : HasGeometricCMCollision P h6, Subgroup)
    (actionData : ∀ h : HasGeometricCMCollision P h6,
      OrientedSpecializedActions CM
        (common_root_specialization P h6 CM hE8 rootData h))
    (normData : HasGeometricCMCollision P h6 → CommonNormData n)
    (normalization : ∀ h : HasGeometricCMCollision P h6,
      LevelSixCovolumeNormalization ℓ (normData h).norm EC
        (collisionCurve h) (levelSubgroup h)
        (CM.specializedAction
          (common_root_specialization P h6 CM hE8 rootData h).numeratorPoint)
        (CM.specializedAction
          (common_root_specialization P h6 CM hE8 rootData h).denominatorPoint))
    (hsmall : (n + 1) ^ 2 < 24 * ℓ) :
    IsCoprime (reduceAwaySixPolynomial ℓ h6 P.numerator)
      (reduceAwaySixPolynomial ℓ h6 P.denominator) := by
  letI : Fact ℓ.Prime := ⟨hprime⟩
  by_contra hnot
  have hcollision : HasGeometricCMCollision P h6 := by
    rw [hasGeometricCMCollision_iff]
    exact (SptCM.not_isCoprime_reductions_iff_collision P h6).mp hnot
  obtain ⟨m, hnorm, hvolume⟩ :=
    common_root_specialization_to_volume P h6 CM EC supersingularCompatible
      hE8 hE9 rootData
      collisionCurve curveEq levelSubgroup actionData normData normalization
      hcollision
  exact SptCM.collision_impossible_of_volume hnorm hvolume hsmall

end

end SptCM.Repair
