# Conditional canonical classification

This package states the canonical congruence-prime classification from Larry
Rolen's [paper](https://arxiv.org/abs/2610.27145v1), relative to the explicit
literature and analytic-model interfaces listed in `ASSUMPTIONS.md` and
`EXTERNAL_INPUTS.json`. The primes are exactly 5, 7, and 13. It does not
formalize all of those external inputs. The exact theorem-level citations for
E8 remain an acknowledged documentation gap.

`Challenge.lean` defines the mathematical statement and every project-specific
premise without importing the proof library. `Solution.lean` imports the original
proof. `comparator.json` selects the classification and two supporting geometric
lemmas used to form its definitions; the corresponding Challenge proofs are
intentional holes. The Solution proofs use only `propext`, `Classical.choice`,
and `Quot.sound`.

The preparation upgrades Lean and Mathlib to 4.35.0-rc2, ports the library to
public modules and exposed definitions, and adapts changed library interfaces.
It disables an overlapping generic additive-group instance where necessary to
retain the standard ring structure. No literature premise is removed.

The Challenge is formatted compactly to meet Palomar's 1,000-line limit.
Its eight `run_cmd` commands clear Lean's elaboration-only auxiliary-lemma
cache at selected original file boundaries. This preserves the generated proof
names used by the original definitions when those definitions are collected in
one file. These commands neither add axioms nor change the proof checker.

Local validation: the upgraded SptCM library builds; the classification axiom
audit contains only the three axioms above; the local comparison of theorem
types and reachable definition bodies passes. These checks are not a substitute
for Palomar's full workflow, including the independent NanoDa checker. The
workflow report for the exact submitted commit records that result.

No human alignment review is claimed. Registration and the resulting public
review record are separate from mechanical validation.
