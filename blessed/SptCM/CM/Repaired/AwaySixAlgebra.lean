module

public import blessed.SptCM.CM.ActualClassPolynomials
public import Mathlib.RingTheory.Localization.FractionRing

public section

-- Use the standard additive structure already supplied by the ring instance.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace SptCM.CM.Repaired
noncomputable section

@[expose]
def awaySixToRat : SptCM.AwaySix →+* ℚ :=
  Localization.awayLift (Int.castRingHom ℚ) 6 (by norm_num)

@[expose]
instance awaySixDomain : IsDomain SptCM.AwaySix :=
  Localization.Away.isDomain (by norm_num)

/-- The canonical `ℤ[1/6]`-algebra structure on every rational algebra. -/
@[expose]
instance awaySixAlgebra (L : Type*) [CommRing L] [Algebra ℚ L] :
    Algebra SptCM.AwaySix L :=
  ((algebraMap ℚ L).comp awaySixToRat).toAlgebra

lemma awaySixToRat_injective : Function.Injective awaySixToRat := by
  unfold awaySixToRat Localization.awayLift IsLocalization.Away.lift
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    have hz := congrArg awaySixToRat h
    simpa [awaySixToRat] using hz
  · intro h
    have hxy : x = y := Int.cast_injective h
    subst y
    rfl

@[expose]
instance awaySixRatFractionRing : IsFractionRing SptCM.AwaySix ℚ := by
  apply IsLocalization'.mk
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    apply nonZeroDivisors.ne_zero y.2
    apply awaySixToRat_injective
    rw [RingHom.algebraMap_toAlgebra] at hy
    simpa using hy
  · intro z
    obtain ⟨xy, hxy⟩ := IsLocalization.surj (nonZeroDivisors ℤ) z
    refine ⟨(algebraMap ℤ SptCM.AwaySix xy.1,
      ⟨algebraMap ℤ SptCM.AwaySix xy.2, ?_⟩), ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hz
      have hp : Submonoid.powers (6 : ℤ) ≤ nonZeroDivisors ℤ := by
        intro a ha
        rcases ha with ⟨n, rfl⟩
        exact mem_nonZeroDivisors_iff_ne_zero.mpr
          (pow_ne_zero n (by norm_num))
      have hz' : (xy.2 : ℤ) = 0 := by
        apply IsLocalization.injective SptCM.AwaySix hp
        simpa using hz
      exact nonZeroDivisors.ne_zero xy.2.property hz' 
    · simpa [awaySixToRat, RingHom.algebraMap_toAlgebra] using hxy
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp [awaySixToRat_injective hxy]


/-- The canonical maps `ℤ[1/6] → ℚ → L` form a scalar tower. -/
@[expose]
instance awaySixRatScalarTower (L : Type*) [CommRing L] [Algebra ℚ L] :
    IsScalarTower SptCM.AwaySix ℚ L := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The previously used concrete embedding into `ℂ` is the algebra map from
the canonical rational-algebra structure. -/
theorem awaySixToComplex_eq_algebraMap :
    SptCM.awaySixToComplex = algebraMap SptCM.AwaySix ℂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (6 : ℤ))
  ext z
  simp [SptCM.awaySixToComplex]
end
end SptCM.CM.Repaired
