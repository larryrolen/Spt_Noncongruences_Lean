import blessed.SptCM.Analytic.Repaired.HeckePrincipalParts
import blessed.SptCM.Analytic.Repaired.GridHeckePrincipalParts
import blessed.SptCM.Analytic.ChiTwelve

/-!
# Source-faithful application of the I05 Hecke inputs

The external boundary in this module carries only the modular/shadow
qualification of the two concrete normalized left sides.  The Fourier
principal parts, quadratic-character arithmetic, uniqueness deductions, and
the resulting identities are proved internally.
-/

namespace SptCM.Analytic.Repaired

open SptCM.Analytic
open SptCM.RolenLiterature

/-- The actual Legendre symbol made total in the index `p`; all I05 uses
specialize it at a prime. -/
def actualHeckeLegendre {K : Type*} [Field K] (p : ℕ) (r : ℤ) : K :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    heckeLegendreCast p r
  else 0

/-- At a prime the total wrapper is the usual cast Legendre symbol. -/
theorem actualHeckeLegendre_eq {K : Type*} [Field K]
    (p : ℕ) (hp : p.Prime) (r : ℤ) :
    actualHeckeLegendre (K := K) p r =
      @heckeLegendreCast K _ p ⟨hp⟩ r := by
  simp [actualHeckeLegendre, hp]

/-- The total wrapper takes the value one at `1` for primes. -/
theorem actualHeckeLegendre_one {K : Type*} [Field K]
    (p : ℕ) (hp : p.Prime) : actualHeckeLegendre (K := K) p 1 = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [actualHeckeLegendre, hp, heckeLegendreCast_one]

/-- The exact square-symbol law for the total wrapper at primes. -/
theorem actualHeckeLegendre_square {K : Type*} [Field K]
    (p : ℕ) (hp : p.Prime) (a : ℤ) :
    actualHeckeLegendre (K := K) p (a ^ 2) =
      if (p : ℤ) ∣ a then 0 else 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [actualHeckeLegendre, hp, heckeLegendreCast_square]

/-- The actual normalized left side of the `f`-Hecke identity. -/
def actualFHeckeLeft {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (p : ℕ) : QSeries K :=
  fun r => (p : K)⁻¹ *
    fHeckeDifference p (G.chi p) (actualHeckeLegendre p)
      (fun s => (fSeries s : K)) r

/-- The actual right side of the normalized `f`-Hecke identity. -/
def actualFHeckeRight {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (p : ℕ) : QSeries K :=
  G.grid p

/-- The actual normalized left side of the grid Hecke recurrence. -/
def actualGridHeckeLeft {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (m p : ℕ) : QSeries K :=
  normalizedGridHeckeLeft p m G.chi (actualHeckeLegendre p) G.grid

/-- The actual right side of the normalized grid Hecke recurrence. -/
def actualGridHeckeRight {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (m p : ℕ) : QSeries K :=
  G.grid (m * p)

/-- Exact E3/E4 application boundary used in I05.  These are only the
modular/shadow qualifications supplied by the cited analytic theory; neither
a principal-part assertion nor either desired Hecke identity is a field. -/
structure SourceI05Qualification {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) : Prop where
  f_left_qualifies : ∀ p, ValidLevelPrime p →
    G.Qualifies p (actualFHeckeLeft G p)
  grid_left_qualifies : ∀ m p, 1 < m → Nat.Coprime m 6 →
    ValidLevelPrime p →
      G.Qualifies (m * p) (actualGridHeckeLeft G m p)

/-- The published character has value one at the unit index. -/
theorem publishedChi_one {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) : G.chi 1 = 1 := by
  rw [G.chi_eq_chi12]
  norm_num [chi12]

/-- Multiplicativity of the published character is internal finite residue
arithmetic, transported through its exact identification with `χ₁₂`. -/
theorem publishedChi_mul {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (a b : ℕ) :
    G.chi (a * b) = G.chi a * G.chi b := by
  rw [G.chi_eq_chi12, G.chi_eq_chi12, G.chi_eq_chi12]
  exact chi12_nat_mul_cast a b

/-- In the valid Hecke range the published character has square one. -/
theorem publishedChi_sq {K : Type*} [Field K]
    (G : PublishedMockModularGrid K) (p : ℕ) (hp6 : Nat.Coprime p 6) :
    G.chi p * G.chi p = 1 := by
  rw [G.chi_eq_chi12]
  simpa [pow_two] using
    (chi12_nat_sq_cast_of_coprime_six (K := K) p hp6)

/-- The exact qualification record for the concrete sides is assembled from
only the cited modular/shadow qualification input and internally checked
principal parts. -/
def actualHeckeQualificationData {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G) :
    HeckeQualificationData G where
  f := fun r => (fSeries r : K)
  fHeckeLeft := actualFHeckeLeft G
  fHeckeRight := actualFHeckeRight G
  gridHeckeLeft := actualGridHeckeLeft G
  gridHeckeRight := actualGridHeckeRight G
  f_left_qualifies := Q.f_left_qualifies
  f_right_qualifies := by
    intro p hp
    exact G.qualifies_grid p hp.1.one_lt hp.2
  f_left_principalPart := by
    intro p hp
    exact actualFHeckeDifference_hasGridPrincipalPart p hp.1 G.chi
      (actualHeckeLegendre p) (actualHeckeLegendre_one p hp.1)
  f_right_principalPart := by
    intro p hp
    exact G.principalPart p hp.1.one_lt hp.2
  grid_left_qualifies := Q.grid_left_qualifies
  grid_right_qualifies := by
    intro m p hm hm6 hp
    have hmp : 1 < m * p :=
      Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m hp.1.pos)
    exact G.qualifies_grid (m * p) hmp (hm6.mul_left hp.2)
  grid_left_principalPart := by
    intro m p hm hm6 hp
    apply normalizedGridHeckeLeft_hasGridPrincipalPart G.chi
      (actualHeckeLegendre p) G.grid
      (publishedChi_one G) (publishedChi_mul G) m p G.grid_one
      (G.principalPart m hm hm6)
      (G.principalPart p hp.1.one_lt hp.2)
    · intro hpm q hq hq1
      subst q
      have hqdvd : m / p ∣ m := Nat.div_dvd_of_dvd hpm
      exact G.principalPart (m / p) hq1
        (Nat.Coprime.of_dvd_left hqdvd hm6)
    · exact hm
    · exact hp.1
    · exact Nat.cast_ne_zero.mpr hp.1.ne_zero
    · exact publishedChi_sq G p hp.2
    · exact actualHeckeLegendre_one p hp.1
    · exact actualHeckeLegendre_square p hp.1
  grid_right_principalPart := by
    intro m p hm hm6 hp
    have hmp : 1 < m * p :=
      Nat.lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m hp.1.pos)
    exact G.principalPart (m * p) hmp (hm6.mul_left hp.2)

/-- The exact concrete qualification package exists from the citation-level
modular/shadow input: every principal-part field and every right-side
qualification is discharged internally above. -/
theorem actualHeckeQualificationData_exists
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G) :
    Nonempty (HeckeQualificationData G) :=
  ⟨actualHeckeQualificationData G Q⟩

/-- I05 with the actual series and source normalizations.  The conclusion is
derived by uniqueness; it is not stored in the external qualification input. -/
theorem actual_source_hecke_identities
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G) :
    (∀ p, ValidLevelPrime p →
      actualFHeckeLeft G p = actualFHeckeRight G p) ∧
    (∀ m p, 1 < m → Nat.Coprime m 6 → ValidLevelPrime p →
      actualGridHeckeLeft G m p = actualGridHeckeRight G m p) := by
  simpa only [HeckeIdentitySpec, actualHeckeQualificationData] using
    published_hecke_identities G (actualHeckeQualificationData G Q)

/-- The first component is Rolen's `f`-Hecke identity in normalized form. -/
theorem actual_f_hecke_identity
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G)
    (p : ℕ) (hp : ValidLevelPrime p) :
    actualFHeckeLeft G p = actualFHeckeRight G p :=
  (actual_source_hecke_identities G Q).1 p hp

/-- The second component is Rolen's grid recurrence, solved for `G_{mp}` and
valid for every source-allowed `m` and Hecke prime. -/
theorem actual_grid_hecke_identity
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G)
    (m p : ℕ) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (hp : ValidLevelPrime p) :
    actualGridHeckeLeft G m p = actualGridHeckeRight G m p :=
  (actual_source_hecke_identities G Q).2 m p hm hm6 hp


/-- Rolen's first displayed identity, with the normalization cleared. -/
theorem actual_f_hecke_identity_displayed
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G)
    (p : ℕ) (hp : ValidLevelPrime p) :
    fHeckeDifference p (G.chi p) (actualHeckeLegendre p)
        (fun s => (fSeries s : K)) =
      fun r => (p : K) * G.grid p r := by
  have h := actual_f_hecke_identity G Q p hp
  funext r
  have hr := congrFun h r
  simp only [actualFHeckeLeft, actualFHeckeRight] at hr
  field_simp [Nat.cast_ne_zero.mpr hp.1.ne_zero] at hr
  exact hr

/-- Rolen's second displayed identity, with the normalized recurrence expanded
and the leading `p G_{mp}` term restored to the right side. -/
theorem actual_grid_hecke_identity_displayed
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G)
    (m p : ℕ) (hm : 1 < m) (hm6 : Nat.Coprime m 6)
    (hp : ValidLevelPrime p) :
    heckeThreeHalf p (G.chi p) (actualHeckeLegendre p) (G.grid m) =
      fun r =>
        (p : K) * G.grid (m * p) r +
        G.chi p * actualHeckeLegendre p ((m : ℤ) ^ 2) * G.grid m r +
        gridDivisorTerm G.grid m p r -
        (p : K) * G.chi m * G.grid p r := by
  have h := actual_grid_hecke_identity G Q m p hm hm6 hp
  funext r
  have hr := congrFun h r
  simp only [actualGridHeckeLeft, actualGridHeckeRight,
    normalizedGridHeckeLeft] at hr
  field_simp [Nat.cast_ne_zero.mpr hp.1.ne_zero] at hr
  linear_combination hr


/-- The two source-displayed Hecke identities, with no identity hidden in an
input record and with every source range explicit. -/
theorem actual_source_hecke_identities_displayed
    {K : Type*} [Field K] [CharZero K]
    (G : PublishedMockModularGrid K) (Q : SourceI05Qualification G) :
    (∀ p, ValidLevelPrime p →
      fHeckeDifference p (G.chi p) (actualHeckeLegendre p)
          (fun s => (fSeries s : K)) =
        fun r => (p : K) * G.grid p r) ∧
    (∀ m p, 1 < m → Nat.Coprime m 6 → ValidLevelPrime p →
      heckeThreeHalf p (G.chi p) (actualHeckeLegendre p) (G.grid m) =
        fun r =>
          (p : K) * G.grid (m * p) r +
          G.chi p * actualHeckeLegendre p ((m : ℤ) ^ 2) * G.grid m r +
          gridDivisorTerm G.grid m p r -
          (p : K) * G.chi m * G.grid p r) := by
  exact ⟨actual_f_hecke_identity_displayed G Q,
    actual_grid_hecke_identity_displayed G Q⟩

end SptCM.Analytic.Repaired
