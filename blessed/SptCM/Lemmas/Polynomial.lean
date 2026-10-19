import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Algebra.Field.ZMod

namespace SptCM

open Polynomial

/-- The Wronskian obstruction, with the paper's convention `A' B - A B'`. -/
noncomputable def wronskianObstruction {R : Type*} [CommRing R]
    (A B : Polynomial R) : Polynomial R :=
  derivative A * B - A * derivative B

/-- A monic polynomial of positive degree below a prime characteristic cannot
have zero derivative. Hence a coprime pair has nonzero paper Wronskian. -/
theorem wronskianObstruction_ne_zero_zmod
    {p : ℕ} (hp : p.Prime) {A B : Polynomial (ZMod p)}
    (hcop : IsCoprime A B) (hmonic : A.Monic)
    (hpos : 0 < A.natDegree) (hlt : A.natDegree < p) :
    wronskianObstruction A B ≠ 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro hW
  have hw : A.wronskian B = 0 := by
    have hsign : wronskianObstruction A B = -A.wronskian B := by
      simp [wronskianObstruction, Polynomial.wronskian]
    rw [hsign] at hW
    exact neg_eq_zero.mp hW
  have hder : derivative A = 0 := (hcop.wronskian_eq_zero_iff.mp hw).1
  have hcoeff := congrArg (fun Q : Polynomial (ZMod p) =>
    Q.coeff (A.natDegree - 1)) hder
  rw [coeff_derivative, coeff_zero] at hcoeff
  have hdegree : A.natDegree - 1 + 1 = A.natDegree :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')
  have hcast : ((A.natDegree - 1 : ℕ) : ZMod p) + 1 =
      (A.natDegree : ZMod p) := by
    calc
      ((A.natDegree - 1 : ℕ) : ZMod p) + 1 =
          ((A.natDegree - 1 + 1 : ℕ) : ZMod p) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = (A.natDegree : ZMod p) := by rw [hdegree]
  rw [hdegree, hmonic.coeff_natDegree, one_mul, hcast] at hcoeff
  have hdvd : p ∣ A.natDegree :=
    (ZMod.natCast_eq_zero_iff A.natDegree p).mp hcoeff
  exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hpos hdvd)

end SptCM
