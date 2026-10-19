import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Polynomial descent in a finite Galois extension

This is the general algebraic descent used by the CM class-polynomial
argument.  It is independent of Rolen's forms and Hauptmodul: a polynomial
whose coefficients are fixed by the full Galois group comes from the base
field.  The fixed-field step is Mathlib's exact theorem
`IsGalois.mem_range_algebraMap_iff_fixed`.
-/

namespace SptCM.CM.Repaired

open Polynomial

/-- A polynomial over a finite Galois extension descends to the base field if
it is fixed coefficientwise by every Galois automorphism. -/
theorem exists_basePolynomial_of_galois_fixed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (p : E[X])
    (hfixed : ∀ σ : E ≃ₐ[F] E, p.map σ.toRingEquiv.toRingHom = p) :
    ∃ q : F[X], q.map (algebraMap F E) = p := by
  change p ∈ (Polynomial.mapRingHom (algebraMap F E)).range
  rw [Polynomial.mem_map_range]
  intro i
  change p.coeff i ∈ Set.range (algebraMap F E)
  apply (IsGalois.mem_range_algebraMap_iff_fixed (p.coeff i)).2
  intro σ
  have hi := congrArg (fun f : E[X] => f.coeff i) (hfixed σ)
  simpa using hi

end SptCM.CM.Repaired

namespace SptCM.CM.Repaired

open Polynomial

/-- If a polynomial over an extension field descends to the fraction field of
an integrally closed domain and all of its coefficients are integral over the
domain, then it already descends to the domain. -/
theorem exists_integrallyClosedPolynomial_of_fractional_integral
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (p : L[X])
    (hrat : ∃ q : K[X], q.map (algebraMap K L) = p)
    (hint : ∀ i, IsIntegral A (p.coeff i)) :
    ∃ P : A[X], P.map (algebraMap A L) = p := by
  change p ∈ (Polynomial.mapRingHom (algebraMap A L)).range
  rw [Polynomial.mem_map_range]
  intro i
  obtain ⟨q, hq⟩ := hrat
  have hcoeff : algebraMap K L (q.coeff i) = p.coeff i := by
    have := congrArg (fun f : L[X] => f.coeff i) hq
    simpa using this
  have hqint : IsIntegral A (q.coeff i) := by
    apply (isIntegral_algebraMap_iff
      (FaithfulSMul.algebraMap_injective K L)).mp
    rw [hcoeff]
    exact hint i
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨a, ?_⟩
  rw [← hcoeff, ← ha, IsScalarTower.algebraMap_apply A K L]

end SptCM.CM.Repaired
