import blessed.SptCM.Arithmetic.SmallDiscriminant
import blessed.SptCM.Literature.RolenLiterature
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The genuine Dirichlet-character bridge for Treviño's estimate

This file packages the quadratic character of `ZMod ℓ` as a complex-valued
Dirichlet character, proves that its integer evaluations are the complex casts
of Legendre symbols, and uses that identification to feed the constant
interval already proved in `SmallDiscriminant` to the corrected E10 estimate.
-/

namespace SptCM.Repair

open SptCM.RolenLiterature

/-- The complex quadratic Dirichlet character modulo a prime. -/
noncomputable def complexQuadraticCharacter (ℓ : ℕ) [Fact ℓ.Prime] :
    DirichletCharacter ℂ ℓ :=
  MulChar.ofUnitHom <|
    (Units.map (Int.castRingHom ℂ).toMonoidHom).comp
      (quadraticChar (ZMod ℓ)).toUnitHom

/-- Integer evaluation of the complex quadratic character is the complex cast
of the Legendre symbol. -/
theorem complexQuadraticCharacter_apply_int
    (ℓ : ℕ) [Fact ℓ.Prime] (a : ℤ) :
    complexQuadraticCharacter ℓ (a : ZMod ℓ) = (legendreSym ℓ a : ℂ) := by
  rw [legendreSym]
  by_cases ha : IsUnit (a : ZMod ℓ)
  · obtain ⟨u, hu⟩ := ha
    rw [← hu]
    simp [complexQuadraticCharacter]
  · rw [MulChar.map_nonunit _ ha]
    have hzero : quadraticChar (ZMod ℓ) (a : ZMod ℓ) = 0 :=
      MulChar.map_nonunit _ ha
    rw [hzero]
    norm_num

/-- At primes in the paper's range the genuine complex quadratic character is
not the principal Dirichlet character. -/
theorem complexQuadraticCharacter_ne_one
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    complexQuadraticCharacter ℓ ≠ 1 := by
  have hℓtwo : ℓ ≠ 2 := by
    have : 2 < SptCM.cutoff := by norm_num [SptCM.cutoff]
    omega
  have hchar : ringChar (ZMod ℓ) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hℓtwo
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one hchar
  have hxunit : IsUnit x := by
    by_contra hxnot
    have hxzero : quadraticChar (ZMod ℓ) x = 0 :=
      MulChar.map_nonunit _ hxnot
    rw [hx] at hxzero
    norm_num at hxzero
  obtain ⟨u, rfl⟩ := hxunit
  intro hprincipal
  have heval : complexQuadraticCharacter ℓ (u : ZMod ℓ) = (-1 : ℂ) := by
    have h := complexQuadraticCharacter_apply_int ℓ ((u : ZMod ℓ).val : ℤ)
    simpa [legendreSym, ZMod.natCast_zmod_val, hx] using h
  have hone : complexQuadraticCharacter ℓ (u : ZMod ℓ) = 1 := by
    simpa using congrArg
      (fun χ : DirichletCharacter ℂ ℓ => χ (u : ZMod ℓ)) hprincipal
  rw [hone] at heval
  norm_num at heval

/-- The shifted Legendre-symbol interval is exactly a constant interval for the
genuine complex Dirichlet character. -/
theorem constant_complexQuadraticCharacter_interval
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    let c : ℤ := SptCM.inverse24Index ℓ
    ConstantDirichletOnInterval (complexQuadraticCharacter ℓ)
      (1 - c) (SptCM.firstNonresidue ℓ - 1) := by
  dsimp only
  let c : ℤ := SptCM.inverse24Index ℓ
  have hc : (24 : ZMod ℓ) * (c : ZMod ℓ) = 1 := by
    dsimp [c]
    simpa only [Int.cast_natCast] using (SptCM.inverse24Index_spec hlarge).2
  have hex := SptCM.firstNonresidue_exists hlarge
  let k := SptCM.firstNonresidue ℓ
  intro i j hi hj
  have hi' : i + 1 < k := by
    have hkpos : 0 < k := (SptCM.firstNonresidue_spec hex).1
    omega
  have hj' : j + 1 < k := by
    have hkpos : 0 < k := (SptCM.firstNonresidue_spec hex).1
    omega
  have hci := SptCM.character_interval c hc hex (Nat.succ_pos i) hi'
  have hcj := SptCM.character_interval c hc hex (Nat.succ_pos j) hj'
  dsimp [c] at hci hcj
  rw [← Int.cast_add, ← Int.cast_add]
  rw [complexQuadraticCharacter_apply_int,
    complexQuadraticCharacter_apply_int]
  congr 1
  convert hci.trans hcj.symm using 1 <;> ring

/-- E10 applied to the actual quadratic Dirichlet character gives the exact
real first-nonresidue bound used by the rest of the project. -/
theorem firstNonresidue_bound_of_E10
    (hE10 : E10TrevinoCorrected)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    (SptCM.firstNonresidue ℓ : ℝ) ≤
      3.38 * (ℓ : ℝ) ^ (1 / 4 : ℝ) * Real.log ℓ + 1 := by
  let c : ℤ := SptCM.inverse24Index ℓ
  let k := SptCM.firstNonresidue ℓ
  have hconstant : ConstantDirichletOnInterval
      (complexQuadraticCharacter ℓ) (1 - c) (k - 1) := by
    simpa [c, k] using constant_complexQuadraticCharacter_interval hlarge
  have hbound := hE10 ℓ (k - 1) (complexQuadraticCharacter ℓ) (1 - c)
    (Fact.out : ℓ.Prime) (complexQuadraticCharacter_ne_one hlarge) hconstant
  have hex := SptCM.firstNonresidue_exists hlarge
  have hkpos : 0 < k := (SptCM.firstNonresidue_spec hex).1
  have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    norm_cast
    omega
  dsimp [k] at hbound ⊢
  rw [← hkcast]
  linarith

/-- Combining the genuine-character E10 bridge with the elementary tail in
`SmallDiscriminant` produces the exact bounded minimal inert progression
member required by the project. -/
theorem smallInertCandidate_of_E10
    (hE10 : E10TrevinoCorrected)
    {ℓ : ℕ} [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    ∃ n : ℕ,
      0 < n ∧ n % 24 = 23 ∧ ¬ IsSquare (-(n : ZMod ℓ)) ∧
      (n + 1) ^ 2 < 24 * ℓ ∧
      ∀ m : ℕ, 0 < m → m < n →
        ¬ (m % 24 = 23 ∧ ¬ IsSquare (-(m : ZMod ℓ))) := by
  let k := SptCM.firstNonresidue ℓ
  have hex := SptCM.firstNonresidue_exists hlarge
  have hkspec := SptCM.firstNonresidue_spec hex
  have hkbound := firstNonresidue_bound_of_E10 hE10 hlarge
  have hksq := SptCM.progression_index_square_lt hlarge hkbound
  let n := 24 * k - 1
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hnadd : n + 1 = 24 * k := by
    dsimp [n]
    omega
  have hnsq : (n + 1) ^ 2 < 24 * ℓ := by
    rw [hnadd]
    exact hksq
  have hnmod : n % 24 = 23 := by
    dsimp [n]
    omega
  have hnlt : n < ℓ :=
    SptCM.n_lt_modulus_of_succ_sq_lt
      (by
        have : 24 < SptCM.cutoff := by norm_num [SptCM.cutoff]
        omega)
      hnsq
  have hncast : (n : ZMod ℓ) ≠ 0 := by
    intro hz
    have hdvd : ℓ ∣ n := (ZMod.natCast_eq_zero_iff n ℓ).mp hz
    have := Nat.le_of_dvd hnpos hdvd
    omega
  have hnum : (1 : ℤ) - 24 * (k : ℤ) = -(n : ℤ) := by
    dsimp [n]
    omega
  have hcharneg : legendreSym ℓ (-(n : ℤ)) = -1 := by
    rw [← hnum]
    apply (legendreSym.eq_neg_one_iff_not_one ℓ ?_).2 hkspec.2
    rw [hnum]
    push_cast
    exact neg_ne_zero.mpr hncast
  have hinert : ¬ IsSquare (-(n : ZMod ℓ)) := by
    have h := (legendreSym.eq_neg_one_iff ℓ).1 hcharneg
    simpa using h
  refine ⟨n, hnpos, hnmod, hinert, hnsq, ?_⟩
  intro m hmpos hmlt hmprop
  rcases hmprop with ⟨hmmod, hminert⟩
  let j := (m + 1) / 24
  have hmadd : m + 1 = 24 * j := by
    dsimp [j]
    omega
  have hjpos : 0 < j := by omega
  have hjlt : j < k := by
    dsimp [n] at hmlt
    omega
  have hmchar : legendreSym ℓ (-(m : ℤ)) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using hminert
  have hinterval := SptCM.character_interval_progression hex hjpos hjlt
  have harg : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ) := by
    exact_mod_cast
      (by omega : (1 : ℤ) - 24 * (j : ℤ) = -(m : ℤ))
  rw [harg] at hinterval
  omega

/-- E10 alone supplies the uniform bounded-candidate input; there is no
separate nonprincipality premise. -/
theorem smallInertCandidateInput_of_E10
    (hE10 : E10TrevinoCorrected) :
    SptCM.SmallInertCandidateInput := by
  intro ℓ hprime hlarge
  letI : Fact ℓ.Prime := ⟨hprime⟩
  exact smallInertCandidate_of_E10 hE10 hlarge

/-- With the independent reduced-form class-number estimate, E10 now reaches
the project's complete small-discriminant interface. -/
theorem smallDiscriminantInput_of_E10
    (h : ℕ → ℕ) (hE10 : E10TrevinoCorrected)
    (hclass : SptCM.ClassNumberEstimateInput h) :
    SptCM.SmallDiscriminantInput h :=
  SptCM.smallDiscriminantInput_of_components h
    (smallInertCandidateInput_of_E10 hE10)
    SptCM.primeSquareInvarianceInput hclass

/-- For the project's concrete reduced-form class number, the remaining
class-number estimate is already proved internally.  Thus E10 by itself
supplies the complete small-discriminant package used by the high-prime
contradiction. -/
theorem negativeClassNumber_smallDiscriminantInput_of_E10
    (hE10 : E10TrevinoCorrected) :
    SptCM.SmallDiscriminantInput SptCM.negativeClassNumber := by
  apply smallDiscriminantInput_of_E10 SptCM.negativeClassNumber hE10
  intro n _ hsquarefree hmod
  exact ⟨SptCM.negativeClassNumber_pos hmod,
    SptCM.class_number_bound hsquarefree hmod⟩

/-- Source-faithful small-discriminant theorem with no arbitrary character
predicate: the only premise is Treviño's corrected E10 statement. -/
theorem small_n_of_E10
    (hE10 : E10TrevinoCorrected)
    (ℓ : ℕ) [Fact ℓ.Prime] (hlarge : SptCM.cutoff ≤ ℓ) :
    ∃ n : ℕ,
      Squarefree n ∧ n % 24 = 23 ∧
      legendreSym ℓ (-(n : ℤ)) = -1 ∧
      (n + 1) ^ 2 < 24 * ℓ ∧
      0 < 2 * SptCM.negativeClassNumber n ∧
      2 * SptCM.negativeClassNumber n < ℓ := by
  obtain ⟨n, hadmissible, hsq, hpos, hlt⟩ :=
    negativeClassNumber_smallDiscriminantInput_of_E10 hE10
      ℓ Fact.out hlarge
  have hinert : legendreSym ℓ (-(n : ℤ)) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa using hadmissible.2.2
  exact ⟨n, hadmissible.1, hadmissible.2.1, hinert, hsq, hpos, hlt⟩

end SptCM.Repair
