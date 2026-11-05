# Explicit Assumption Register

**Assembled by Axiom Prover.**

## Status of the result

The theorem `SptCM.Repair.rolen_spt_classification` is a complete Lean proof
**relative to** the source-facing literature interfaces E1–E11 and the
standard analytic/model-comparison structures described below. These inputs
are represented as explicit theorem premises or fields of premise
structures; they are not hidden global Lean axioms.

## Published and standard inputs E1–E11

### E1 — Andrews congruences

The canonical smallest-parts congruences at primes 5, 7, and 13, from
G. E. Andrews, *J. Reine Angew. Math.* 624 (2008), 133–142.

### E2 — Ahlgren–Kim finite exclusion and theta cycle

The finite exclusion theorem and theta-cycle result from S. Ahlgren and
B. Kim, *J. Number Theory* 189 (2018), Theorem 3 and Proposition 6.

### E3 — Harmonic Maass completion and Hecke/shadow law

Bringmann's harmonic Maass completion of the smallest-parts generating
function and the corresponding Hecke/shadow intertwining law, using
K. Bringmann, *Duke Math. J.* 144 (2008), and the treatment in
Bringmann–Folsom–Ono–Rolen, AMS Colloquium Publications 64 (2017).

### E4 — Standard eta, j, Eisenstein, grid, Hecke, and residue theory

The standard transformation and expansion theory for Dedekind eta, the
modular invariant j, Eisenstein series, modular Hecke operators, principal
parts, and the weight-two residue theorem, together with the integral mock
modular grid of Ahlgren–Kim, *Forum Math.* 26 (2014).

The endpoint exposes this material through `EtaJGeneratorBasis`,
`IntegralGridRealization`, and `WeightTwoMultiplicationTheory`.

### E5 — General Borcherds lift

The general Bruinier–Ono Borcherds-lift theorem from J. H. Bruinier and
K. Ono, *Ann. of Math.* 172 (2010), Theorem 6.1.

The normalized E5 application is qualified by vanishing of all four Weyl
vectors. E6 and the checked pairing computation establish this condition
before E5 is used. The prefactor-free Euler expansion is not asserted for
arbitrary vector inputs with potentially nonzero cusp exponents.

### E6 — Weyl-vector formula

The Bruinier–Schwagenscheidt Weyl-vector formula from J. H. Bruinier and
M. Schwagenscheidt, *J. Algebra* 478 (2017), equation (11).

E3, E5, E6, and finite-height Stokes/model comparisons are exposed together
through `UniformActualNormalizedProductPackage`. This structure does **not**
contain the desired normalized product identity as a field; that identity is
derived in Lean.

### E7 — Eta quotients and integral geometry of X₀(6)

Ligozat's eta-quotient results (G. Ligozat, *Courbes modulaires de genre 1*,
1975) and standard integral modular-curve facts for X₀(6) away from 6,
including genus-zero fibers, disjoint cusps, horizontal divisors, absence of
unwanted vertical components, and the integral degree-one criterion.

The normalized-product argument additionally exposes the standard
genus-zero descent theorem as `I12GenusZeroDescentPrinciple`. Its domain is
fixed by `I12UnitaryMeromorphicRealization`: actual meromorphic functions on
the upper half-plane with unitary Gamma_0(6) transformations, convergent
q-expansions, and convergent expansions at all four cusps. The theorem says
that zero cusp orders imply rationality in the actual Hauptmodul.
This analytic descent theorem remains an explicit, unproved input.
It does not assert the Borcherds/class-polynomial identity.

`I12MeromorphicGeometry` ties the interior divisor to actual meromorphic
orders at each Hauptmodul coordinate and ties cusp data to the analytic
expansions. Its rational-function compatibility law uses full point
multiplicities. Rigidity for nonzero rational functions, invariance under
cancellation, the class-polynomial divisor computation, and leading
normalization are proved internally. See `ANALYTIC_BOUNDARY.md`.

### E8 — CM and reduction theory

Standard results on negative quadratic orders, reduced and oriented binary
quadratic forms, ideal classes, finite Galois CM reciprocity, integral CM
class fields, potential good reduction, Deuring inert supersingular
reduction, and specialization injectivity, in the precise oriented level-six
forms encoded by the Lean interfaces.

The residue specialization is correctly typed on the integral closure of
`ℤ[1/6]` in the CM field, not as a map from a characteristic-zero field to a
positive-characteristic field.

### E9 — Level-six Eichler orders and covolume bound

The oriented level-six Eichler-order result of S. Arpin,
*J. Théor. Nombres Bordeaux* 36 (2024), 405–443, and the
Goren–Lauter Hadamard/covolume estimate of E. Z. Goren and K. E. Lauter,
*Ann. Inst. Fourier* 57 (2007), 457–480.

The application-specific noncommutation, local factors 2 and 3, the `6ℓ`
normalization, and the collision contradiction are derived rather than
assumed as final-purpose fields.

### E10 — Corrected Treviño character bound

The explicit character bound of E. Treviño,
*Mosc. J. Comb. Number Theory* 2 (2012), with the correction in volume 7
(2017).

### E11 — Quadratic forms, reciprocity, and Stokes inputs

Standard binary-quadratic-form reduction, quadratic reciprocity, Euler's
criterion, the squarefree cusp classification, and finite-height
Stokes/residue calculus.

## Exact top-level Lean premises

The final theorem quantifies over the following five explicit values:

```text
SptCM.RolenLiterature.Repair.UniformRolenLiterature
SptCM.Analytic.Repaired.EtaJGeneratorBasis
SptCM.Analytic.Repaired.UniformActualNormalizedProductPackage
SptCM.Analytic.Repaired.IntegralGridRealization
SptCM.Analytic.Repaired.WeightTwoMultiplicationTheory
```

`UniformRolenLiterature` consolidates the uniform arithmetic, modular-curve,
CM, reduction, and quaternionic interfaces. The other four structures give
the precise source-facing analytic realizations needed to instantiate E3–E6
and the standard E4 grid/multiplication theory.

## Conclusions that are not assumed

None of the following is an input field of the final literature boundary:

1. the normalized Borcherds/class-polynomial product identity;
2. class-polynomial separation;
3. the common-root collision package;
4. Wronskian vanishing or algebraic nonvanishing;
5. the application-specific volume contradiction;
6. exclusion of all primes above the finite cutoff;
7. the classification of canonical congruence primes.

These are derived in the Lean dependency chain.

## Audit locations

- Machine-readable citations and declaration names:
  `EXTERNAL_INPUTS.json`
- Uniform public literature boundary:
  `blessed/SptCM/Literature/Repair/PublicLedger.lean`
- Derived normalized product chain:
  `blessed/SptCM/Analytic/Repaired/UniformNormalizedProduct.lean`
- Derived Wronskian contradiction:
  `blessed/SptCM/Repair/ActualWronskianContradiction.lean`
- Derived large-prime exclusion and final theorem:
  `blessed/SptCM/Repair/PublicLargeExclusion.lean`
