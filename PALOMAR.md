# Conditional canonical classification

This package states the canonical congruence-prime classification from Larry
Rolen's [paper](https://arxiv.org/abs/2610.27145v1), relative to the explicit
literature, application, and analytic-model interfaces listed in `ASSUMPTIONS.md` and
`EXTERNAL_INPUTS.json`. The primes are exactly 5, 7, and 13. It does not
formalize all of those external inputs. The exact E8 interfaces are additional unproved application assumptions;
CM literature is background motivation, not certified support for these forms.

`Challenge.lean` defines the mathematical statement and every project-specific
premise without importing the proof library. `Solution.lean` imports the original
proof. `comparator.json` selects only the main classification theorem. The supporting
geometric and Laurent-series lemmas are proved prerequisites in Challenge;
they are not separate selected research results. The sole intentional proof
hole is the classification theorem. The Solution proofs use only `propext`, `Classical.choice`,
and `Quot.sound`.

The preparation upgrades Lean and Mathlib to 4.35.0-rc2, ports the library to
public modules and exposed definitions, and adapts changed library interfaces.
It disables an overlapping generic additive-group instance where necessary to
retain the standard ring structure. No literature premise is removed.

The analytic boundary uses actual meromorphic functions with a unitary
Gamma_0(6) transformation law and convergent Laurent and cusp expansions.
Divisors retain each complex Hauptmodul coordinate and its multiplicity.
Rigidity for nonzero rational functions is proved in Lean from polynomial
factorization; it is not a universal assumption about formal Laurent series.
The explicit `I12GenusZeroDescentPrinciple` remains an unproved analytic
input connecting zero cusp orders to rationality in the Hauptmodul.
See `ANALYTIC_BOUNDARY.md` for the exact scope and justification.

The Challenge is formatted compactly to meet Palomar's 1,000-line limit.
Its `run_cmd` commands clear Lean's elaboration-only auxiliary-lemma
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
