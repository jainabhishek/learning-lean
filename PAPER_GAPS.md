# Paper Gap Checklist (PhysRevResearch 7, 023076)

This document maps numbered equations and named claims in the paper to the current Lean code and flags gaps.
Paths point to existing code; "statement only" means a `def ... : Prop` without a proof.

## Section II: Stochastically simulatable channels

- Eq (1) Definition 1: `stochastically_simulatable` in `LearningLean/Quantum/Stochastic.lean`. Definition exists; sampling equivalence proof is blocked by `sorry`.
- Eq (2): no explicit `N_delta_t` definition that matches the paper formula.
- Eq (3) and Eq (4): no explicit `A_i` or `p_i` definitions; only `unitarySamples`/`stochasticSamples` scaffolding in `LearningLean/Quantum/Stochastic.lean`.
- Eq (5): intended by `expected_sampling_eq_stochasticAction`, but `sorry` in `LearningLean/Quantum/Stochastic.lean:79`.

## Section III: Algorithm and error analysis

- Eq (6): `product_formula_error_bound_statement` is statement only in `LearningLean/Quantum/Algorithm.lean`.
- Eq (7): `dissipator_error_bound_statement` is statement only in `LearningLean/Quantum/Algorithm.lean`.
- Eq (8): `product_formula_pauli_bound_statement` is statement only in `LearningLean/Quantum/Algorithm.lean`. The Pauli reduction is only `pauli_norm_reduction_statement` in `LearningLean/Quantum/Norms.lean`.
- Eq (9) Theorem 1 query complexity: `theorem1_query_complexity` is statement only in `LearningLean/Quantum/Algorithm.lean`. The ancilla claim is not encoded.
- Gate complexity statement: `theorem1_gate_complexity` is statement only in `LearningLean/Quantum/Algorithm.lean`.

## Section IV: Extensions

- Eq (10): no explicit time-dependent `N_{t,delta_t}` approximation; `timeDependent_extension` jumps directly to a cost bound in `LearningLean/Quantum/Extensions.lean`.
- Eq (11): `timeOrdered_secondOrder_bound_diamond_statement` is statement only in `LearningLean/Quantum/TimeOrderedMatrix.lean`.
- Eq (12): local noise decomposition `E(rho) = sum_i lambda_i G_0^(i) otimes ...` not formalized.
- Remark 1: `remark_ancilla_bound` is statement only in `LearningLean/Quantum/Extensions.lean` with no Stinespring/Kraus-rank proof.

## Section V.A: Depolarizing dissipation

- Eq (13): partial scaffolding via `globalDepolarizingJumps` and `globalDepolarizingDissipator` in `LearningLean/Quantum/Examples.lean`, but no proof that it matches the Lindblad form.
- Eq (14)-(16): only `global_depolarizing_pauli_norm_statement` in `LearningLean/Quantum/Examples.lean`, statement only.
- Eq (17): `global_depolarizing_example_statement` is statement only in `LearningLean/Quantum/Examples.lean`.
- Eq (18): ancilla cost only appears as part of the statement; no proof.

## Section V.B: Crosstalk in superconducting transmons

- Eq (19): no explicit Hamiltonian definition; only a norm identity assumption in `crosstalk_example_statement`.
- Eq (20): jump operators are not formalized.
- Eq (21): full Lindbladian not formalized.
- Eq (22): `crosstalk_pauli_norm_statement` is statement only in `LearningLean/Quantum/Examples.lean`.
- Eq (23): `crosstalk_example_statement` is statement only in `LearningLean/Quantum/Examples.lean`.

## Section V.C: 1/f dephasing

- Eq (24): dynamics statement is not formalized.
- Eq (25)-(26): `oneOverFWeight` and `oneOverFSample` exist in `LearningLean/Quantum/Examples.lean`, but only `oneOverF_sampling_statement` (statement only) asserts 1/f spectrum.
- Eq (27): no statement of the tensor product structure for `K_delta_t` and `N_{t,delta_t}`.
- Eq (28): `oneOverF_dissipative_taylor_statement` is statement only in `LearningLean/Quantum/Examples.lean`.
- Eq (29): `dephasingOracle` and `dephasingProbability` exist, but no time-indexed sampling theorem.

## Appendix A: Unitary jump operators

- Eq (A1): `randomUnitaryApprox_bound_statement` is statement only in `LearningLean/Quantum/AppendixA.lean`.

## Appendix B: Time-dependent product formula

- Lemma 1, Eq (B1)-(B2): `backward_evolution_bound_diamond_statement` is statement only in `LearningLean/Quantum/TimeOrderedMatrix.lean`.
- Theorem 2 restated, Eq (B3): `timeOrdered_secondOrder_bound_diamond_statement` is statement only in `LearningLean/Quantum/TimeOrderedMatrix.lean`.
- No explicit `T_L(t,s)` or `T_L^{-}(t,s)` definitions; only `TexpOfPicard` scaffolding in `LearningLean/Quantum/TimeOrdered.lean`.

## Cross-cutting gaps and model mismatches

- `LearningLean/Quantum/Stochastic.lean:55` and `LearningLean/Quantum/Stochastic.lean:79` contain `sorry`.
- `LearningLean/Quantum/AllClaims.lean` only `#check`s names; it does not verify proofs.
- `diamondNorm` is defined via a supremum over density matrices only, not all trace-norm-1 operators; this weakens standard diamond-norm properties (`LearningLean/Quantum/Norms.lean`).
- Diamond-norm additivity/submultiplicativity lemmas are missing.
- `CPTP` is defined as "exists Kraus list with trace-preserving" without an equivalence proof to CP/TP or Stinespring (`LearningLean/Quantum/Channels.lean`).
- `PauliDecomposition` is abstract with no concrete Pauli basis or decomposition proof (`LearningLean/Quantum/Norms.lean`).
- The ODE/time-ordered layer uses the Frobenius norm on matrices, with no bridge to diamond-norm bounds (`LearningLean/Quantum/Matrix.lean`, `LearningLean/Quantum/TimeOrdered.lean`).
