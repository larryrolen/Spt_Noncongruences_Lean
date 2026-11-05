module

public import blessed.SptCM.Quaternion.Repaired.CommonRootSeparation

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


/-!
# General Eichler-lattice arithmetic and the I20 normalization

The Goren--Lauter estimate is stated in terms of an abstract covolume and
squared-length model.  This file separates the genuinely general arithmetic
of an Eichler order from the application to Rolen's two specialized CM
endomorphisms.  In particular, the structure below has no distinguished CM
endomorphisms and no field asserting the desired inequality `6ℓ ≤ 4m²`.
-/

namespace SptCM.Repair

noncomputable section

open SptCM.RolenLiterature

/-- General arithmetic attached to the integral lattice of a preserving
Eichler order.  The local-index law is quantified over arbitrary four
integral vectors.  Thus an application must separately prove that its
particular specialized endomorphisms belong to the preserving order and must
compute their reduced norms. -/
structure EichlerLatticeArithmetic
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D) where
  characteristic : Curve → ℕ
  orderLattice : Order → Lattice
  inOrder : Order → D → Prop
  reducedNorm : D → ℚ
  one_mem : ∀ O, inOrder O 1
  mul_mem : ∀ O {x y}, inOrder O x → inOrder O y → inOrder O (x * y)
  reducedNorm_one : reducedNorm 1 = 1
  reducedNorm_mul : ∀ x y, reducedNorm (x * y) = reducedNorm x * reducedNorm y
  reducedNorm_spec : ∀ x,
    algebraMap ℚ D (reducedNorm x) = SptCM.reducedNorm x
  squaredNorm_eq : ∀ x,
    EC.squaredNorm x = 2 * (reducedNorm x : ℝ)
  independent_of_linearIndependent : ∀ a b c d,
    LinearIndependent ℚ ![a, b, c, d] → EC.independent a b c d
  covolume_nonnegative : ∀ a b c d,
    0 ≤ EC.covolume (EC.span a b c d)
  /-- The (reduced-discriminant) local index of an Eichler order. -/
  localIndex : Order → ℕ
  /-- The local contributions at the primes dividing the level. -/
  localIndexAtTwo : Order → ℕ
  localIndexAtThree : Order → ℕ
  /-- The covolume of a maximal order in the ambient quaternion algebra. -/
  maximalOrderCovolume : Curve → ℝ
  /-- General local-to-global index factorization for a level-six Eichler
  order; all local factors away from `2` and `3` are units. -/
  levelSix_localIndex_factorization : ∀ O,
    EC.isEichlerOfLevelSix O →
      localIndex O = localIndexAtTwo O * localIndexAtThree O
  /-- Preserving the distinguished line at `2` has local index `2`. -/
  levelSix_localIndexAtTwo : ∀ O,
    EC.isEichlerOfLevelSix O → localIndexAtTwo O = 2
  /-- Preserving the distinguished line at `3` has local index `3`. -/
  levelSix_localIndexAtThree : ∀ O,
    EC.isEichlerOfLevelSix O → localIndexAtThree O = 3
  /-- General discriminant normalization for a maximal order in the
  supersingular quaternion algebra. -/
  maximalOrderCovolume_eq_characteristic : ∀ E,
    maximalOrderCovolume E = characteristic E
  /-- General finite-index scaling law for the lattice of an Eichler order. -/
  orderLattice_covolume : ∀ E C,
    EC.isEichlerOfLevelSix (EC.preservingOrder E C) →
    EC.covolume (orderLattice (EC.preservingOrder E C)) =
      localIndex (EC.preservingOrder E C) * maximalOrderCovolume E
  span_covolume_lower : ∀ E C a b c d,
    EC.independent a b c d →
    inOrder (EC.preservingOrder E C) a →
    inOrder (EC.preservingOrder E C) b →
    inOrder (EC.preservingOrder E C) c →
    inOrder (EC.preservingOrder E C) d →
    EC.covolume (orderLattice (EC.preservingOrder E C)) ≤
      EC.covolume (EC.span a b c d)

namespace EichlerLatticeArithmetic

/-- The global index is `2 · 3 = 6`.  The two local computations and their
local-to-global assembly are general level-six Eichler-order facts, while the
multiplication is performed here. -/
theorem levelSix_localIndex_eq_six
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    {EC : EichlerCovolumeModel Curve Subgroup Order Lattice D}
    (A : EichlerLatticeArithmetic EC) (O : Order)
    (hEichler : EC.isEichlerOfLevelSix O) :
    A.localIndex O = 6 := by
  rw [A.levelSix_localIndex_factorization O hEichler,
    A.levelSix_localIndexAtTwo O hEichler,
    A.levelSix_localIndexAtThree O hEichler]

/-- The exact `6 · char(E)` covolume follows after the two local index
computations have been combined. -/
theorem preservingOrder_covolume_eq_six_characteristic
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    {EC : EichlerCovolumeModel Curve Subgroup Order Lattice D}
    (A : EichlerLatticeArithmetic EC) (E : Curve) (C : Subgroup)
    (hEichler : EC.isEichlerOfLevelSix (EC.preservingOrder E C)) :
    EC.covolume (A.orderLattice (EC.preservingOrder E C)) =
      6 * A.characteristic E := by
  rw [A.orderLattice_covolume E C hEichler,
    A.levelSix_localIndex_eq_six _ hEichler,
    A.maximalOrderCovolume_eq_characteristic]
  norm_num

/-- If the quaternion-valued reduced norm of an element is the natural
scalar `m`, then the rational reduced norm used in the lattice metric is
literally `m`.  This is the bridge from the internally derived I19 norm
formula to the numerical E9 normalization. -/
theorem reducedNorm_eq_nat_of_internal
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    {EC : EichlerCovolumeModel Curve Subgroup Order Lattice D}
    (A : EichlerLatticeArithmetic EC) (x : D) (m : ℕ)
    (h : SptCM.reducedNorm x = (m : D)) :
    A.reducedNorm x = m := by
  apply (algebraMap ℚ D).injective
  rw [A.reducedNorm_spec, h]
  simp

/-- The general Eichler-lattice laws instantiate every normalization field
needed by the verified covolume inequality.  The application-specific inputs
are only membership of the two CM endomorphisms in the actual preserving
order and their already-computed common norm. -/
theorem levelSixNormalization
    {ℓ m : ℕ}
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D)
    (A : EichlerLatticeArithmetic EC)
    (E : Curve) (C : Subgroup) (α β : D)
    (hchar : A.characteristic E = ℓ)
    (hcyclic : EC.cyclicOfOrderSix C)
    (hnoncomm : ¬ Commute α β)
    (hα : A.inOrder (EC.preservingOrder E C) α)
    (hβ : A.inOrder (EC.preservingOrder E C) β)
    (hnormα : A.reducedNorm α = (m : ℚ))
    (hnormβ : A.reducedNorm β = (m : ℚ)) :
    LevelSixCovolumeNormalization ℓ m EC E C α β where
  cyclic := hcyclic
  independentOfLinearIndependent :=
    A.independent_of_linearIndependent 1 α β (α * β)
  covolumeNonnegative := A.covolume_nonnegative 1 α β (α * β)
  covolumeLower := by
    intro hEichler
    have hLI : LinearIndependent ℚ ![(1 : D), α, β, α * β] :=
      SptCM.noncommuting_lattice_linearIndependent α β hnoncomm
    have hind : EC.independent 1 α β (α * β) :=
      A.independent_of_linearIndependent 1 α β (α * β) hLI
    have horder :=
      A.preservingOrder_covolume_eq_six_characteristic E C hEichler
    have hspan := A.span_covolume_lower E C 1 α β (α * β) hind
      (A.one_mem _) hα hβ (A.mul_mem _ hα hβ)
    rw [horder, hchar] at hspan
    exact hspan
  normOne := by
    rw [A.squaredNorm_eq, A.reducedNorm_one]
    norm_num
  normAlpha := by rw [A.squaredNorm_eq, hnormα]; norm_num
  normBeta := by rw [A.squaredNorm_eq, hnormβ]; norm_num
  normProduct := by
    rw [A.squaredNorm_eq, A.reducedNorm_mul, hnormα, hnormβ]
    norm_num
    ring

/-- Consequently Arpin's level-six identification and the general
Goren--Lauter lattice laws imply the exact numerical estimate used in I20.
No covolume lower bound or squared-norm formula for the distinguished vectors
is supplied by the caller. -/
theorem levelSix_covolume_inequality_of_general_E9
    {ℓ m : ℕ}
    {Curve Subgroup Order Lattice D : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (EC : EichlerCovolumeModel Curve Subgroup Order Lattice D)
    (hE9 : E9ArpinGorenLauter EC)
    (A : EichlerLatticeArithmetic EC)
    (E : Curve) (C : Subgroup) (α β : D)
    (hss : EC.supersingular E)
    (hnoncomm : ¬ Commute α β)
    (hchar : A.characteristic E = ℓ)
    (hcyclic : EC.cyclicOfOrderSix C)
    (hα : A.inOrder (EC.preservingOrder E C) α)
    (hβ : A.inOrder (EC.preservingOrder E C) β)
    (hnormα : A.reducedNorm α = (m : ℚ))
    (hnormβ : A.reducedNorm β = (m : ℚ)) :
    6 * ℓ ≤ 4 * m ^ 2 := by
  exact levelSix_covolume_inequality_of_E9 EC hE9 E C α β hss hnoncomm
    (A.levelSixNormalization EC E C α β hchar hcyclic hnoncomm
      hα hβ hnormα hnormβ)

/-- I20 for the genuine quadratic-order specializations produced by E8.
The common norm `(n+1)/4` is derived from the defining polynomial of the
canonical quadratic order.  Membership of the two actions in the actual
preserving order is transported from E8's level-order theorem.  Thus none of
the four numerical norm entries or the final volume inequality is a caller
hypothesis. -/
theorem actual_specialized_actions_volume_of_E8_E9
    {n ℓ : ℕ}
    {OrderCM IdealClass CMPoint Curve D Subgroup Lattice : Type*}
    [DivisionRing D] [Star D] [Algebra ℚ D]
    (CM : CMTheoryModel OrderCM IdealClass CMPoint Curve D)
    (S : GeometricCMSpecialization CM)
    (E8Q : E8OrientedQuadraticSpecialization n CM)
    (F : CollisionOrientedFormData CM S E8Q)
    (EC : EichlerCovolumeModel Curve Subgroup (Subring D) Lattice D)
    (hE9 : E9ArpinGorenLauter EC)
    (A : EichlerLatticeArithmetic EC)
    (E : Curve) (C : Subgroup)
    (hcurve : E = CM.reduction S.numeratorPoint)
    (supersingularCompatible : ∀ E,
      CM.supersingular E → EC.supersingular E)
    (hchar : A.characteristic E = ℓ)
    (hcyclic : EC.cyclicOfOrderSix C)
    (hlevelOrder : E8Q.levelOrder = EC.preservingOrder E C)
    (hinOrder : ∀ O x, A.inOrder O x ↔ x ∈ O) :
    6 * ℓ ≤ 4 * ((n + 1) / 4) ^ 2 := by
  let O := actualOrientedSpecializedActions_of_E8 CM S E8Q F
  let α := CM.specializedAction S.numeratorPoint
  let β := CM.specializedAction S.denominatorPoint
  have hnoncomm : ¬ Commute α β := by
    exact specialized_actions_noncommute CM S O
  have hss : EC.supersingular E := by
    rw [hcurve]
    exact supersingularCompatible _ S.supersingular
  have hαLevel : α ∈ E8Q.levelOrder := by
    dsimp [α]
    rw [F.numeratorPoint]
    exact E8Q.specializedGenerator_mem_levelOrder F.numeratorForm
  have hβLevel : β ∈ E8Q.levelOrder := by
    dsimp [β]
    rw [F.denominatorPoint]
    exact E8Q.specializedGenerator_mem_levelOrder F.denominatorForm
  have hαOrder : A.inOrder (EC.preservingOrder E C) α := by
    apply (hinOrder _ _).2
    rw [← hlevelOrder]
    exact hαLevel
  have hβOrder : A.inOrder (EC.preservingOrder E C) β := by
    apply (hinOrder _ _).2
    rw [← hlevelOrder]
    exact hβLevel
  have hnormαD :
      SptCM.reducedNorm α = ((((n + 1) / 4 : ℕ)) : D) := by
    dsimp [α]
    rw [F.numeratorPoint, E8Q.specializedGenerator F.numeratorForm]
    exact reducedNorm_map_negativeQuadraticOmega_eq_natCast
      (E8Q.specialize F.numeratorForm)
      (E8Q.conjugationGenerator F.numeratorForm)
  have hnormβD :
      SptCM.reducedNorm β = ((((n + 1) / 4 : ℕ)) : D) := by
    dsimp [β]
    rw [F.denominatorPoint, E8Q.specializedGenerator F.denominatorForm]
    exact reducedNorm_map_negativeQuadraticOmega_eq_natCast
      (E8Q.specialize F.denominatorForm)
      (E8Q.conjugationGenerator F.denominatorForm)
  have hnormα : A.reducedNorm α = (((n + 1) / 4 : ℕ) : ℚ) :=
    A.reducedNorm_eq_nat_of_internal α _ hnormαD
  have hnormβ : A.reducedNorm β = (((n + 1) / 4 : ℕ) : ℚ) :=
    A.reducedNorm_eq_nat_of_internal β _ hnormβD
  exact A.levelSix_covolume_inequality_of_general_E9 EC hE9 E C α β
    hss hnoncomm hchar hcyclic hαOrder hβOrder hnormα hnormβ

end EichlerLatticeArithmetic

end

end SptCM.Repair
