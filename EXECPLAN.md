# Close Formalization Gaps for PhysRevResearch 7, 023076

This ExecPlan is a living document. The sections `Progress`, `Surprises & Discoveries`, `Decision Log`, and `Outcomes & Retrospective` must be kept up to date as work proceeds.

This document must be maintained in accordance with `PLANS.md` at the repository root.

## Purpose / Big Picture

After this change, a reader can run `lake build` and open `LearningLean/Quantum/AllClaims.lean` to see every numbered equation (1)-(29), Appendix A (A1), Appendix B (B1-B3), Definition 1, Theorem 1, Theorem 2, Lemma 1, Remark 1, and the three demonstrations stated and proved in Lean, with no `sorry` or axioms. They can verify this by running `rg -n "\bsorry\b|\baxiom\b" LearningLean` (expecting no matches) and by confirming `lake build` succeeds.

## Progress

- [x] (2026-01-09 05:55Z) Added `PAPER_GAPS.md` checklist mapping paper claims to code.
- [ ] Replace statement-only claims with proved theorems and remove `sorry`.
- [ ] Align the diamond norm and Pauli basis foundations with the paper and prove required lemmas.
- [ ] Formalize Appendix A, Appendix B, extensions, and examples as theorems and update `LearningLean/Quantum/AllClaims.lean`.

## Surprises & Discoveries

- None yet.

## Decision Log

- Decision: Use `PAPER_GAPS.md` as the explicit checklist and update it as each claim becomes proven.
  Rationale: It keeps scope visible and prevents silent omissions.
  Date/Author: 2026-01-09 / Codex.
- Decision: Convert every `_statement` definition into a `theorem` with a proof while keeping names stable.
  Rationale: This preserves existing references while turning placeholders into verified claims.
  Date/Author: 2026-01-09 / Codex.
- Decision: Introduce a dedicated Pauli module rather than keep abstract coefficients.
  Rationale: The paper’s norm bounds depend on explicit Pauli decompositions, so the basis must be concrete.
  Date/Author: 2026-01-09 / Codex.

## Outcomes & Retrospective

Not started.

## Context and Orientation

This repository is a Lean 4 project at `/Users/abhishekjain/my-git/learning-lean` that formalizes a quantum algorithm paper. The main library modules live under `LearningLean/Quantum/`. The current code defines matrices (`LearningLean/Quantum/Matrix.lean`), density matrices (`LearningLean/Quantum/States.lean`), channels and Kraus forms (`LearningLean/Quantum/Channels.lean`), norms (`LearningLean/Quantum/Norms.lean`), time-ordered ODE scaffolding (`LearningLean/Quantum/TimeOrdered.lean` and `LearningLean/Quantum/TimeOrderedMatrix.lean`), stochastic sampling (`LearningLean/Quantum/Stochastic.lean`), the algorithm statements (`LearningLean/Quantum/Algorithm.lean`), appendices (`LearningLean/Quantum/AppendixA.lean`), extensions (`LearningLean/Quantum/Extensions.lean`), and examples (`LearningLean/Quantum/Examples.lean`). The file `LearningLean/Quantum/AllClaims.lean` aggregates the claims with `#check`s. The paper text is in `PhysRevResearch.7.023076.txt`. The gap checklist is in `PAPER_GAPS.md` and must be kept in sync as proofs land.

A density matrix is a complex square matrix that is Hermitian, positive semidefinite, and trace one. A quantum channel is a completely positive, trace-preserving linear map; the code uses Kraus operators (a finite list of matrices) to witness this. The diamond norm is the supremum, over joint system-ancilla states, of the trace norm after applying the channel to the system; it is the metric used in the paper’s error bounds. A Lindbladian is the generator of a Markovian master equation, split into a Hamiltonian commutator term and a dissipator term. A Pauli decomposition expresses a Hamiltonian or Lindbladian in the Pauli basis, with coefficients that define the paper’s Pauli norm. Time-ordered exponentials `T_L(t,s)` and their backward evolutions `T_L^-(t,s)` are the propagators in Appendix B.

## Plan of Work

The plan is to replace each paper statement placeholder with an actual theorem and to strengthen the mathematical foundations so those proofs are meaningful. Start from the checklist in `PAPER_GAPS.md` and move items to “done” as the corresponding theorems compile without `sorry`. First close the Definition 1 sampling gap by proving the expectation lemmas and by adding explicit `A_i` and `p_i` definitions that match equations (2)-(5); this gives a correct probabilistic semantics for the algorithm. Next, strengthen the norm layer so diamond norm properties used in the algorithm and Appendix B are provable; this includes defining the diamond norm in a standard way, proving submultiplicativity and additivity, and making the trace norm lemmas robust. Then specialize the time-ordered evolution results to the matrix setting and prove Lemma 1 and Theorem 2 in diamond norm. After that, formalize the algorithm bounds in equations (6)-(9), including a concrete Pauli basis and a proven Pauli norm reduction. Finally, formalize the extensions and the three demonstrations, connecting each example’s Hamiltonian and dissipator to the earlier definitions and error bounds. Each milestone should end with `lake build` and a small update to `LearningLean/Quantum/AllClaims.lean` so the repository visibly reflects what is now proven.

## Milestones

### Milestone 1: Definition 1 sampling semantics and Eq (2)-(5)

Complete the probabilistic semantics of stochastically simulatable channels. This means replacing the `sorry` proofs in `LearningLean/Quantum/Stochastic.lean` with actual proofs, adding explicit Lean definitions for the operations `A_i` and probabilities `p_i` that match equations (2)-(5), and adding a lemma for repeated independent sampling across `r` gadget applications. At the end of this milestone, running `lake build` should succeed and `LearningLean/Quantum/AllClaims.lean` should `#check` the proved sampling lemma rather than a placeholder.

### Milestone 2: Norm layer and diamond-norm lemmas

Strengthen `LearningLean/Quantum/Norms.lean` so the diamond norm used in the paper has the expected algebraic properties. Decide whether to redefine `diamondNorm` as a supremum over all trace-norm-bounded operators or to prove equivalence to the density-matrix supremum for CPTP maps, and document the choice in the Decision Log. Add theorems for additivity and submultiplicativity of the diamond norm, and ensure the trace norm lemmas are sufficient to use in later proofs. At the end of this milestone, `diamondNorm_additive` and `diamondNorm_submultiplicative` exist as theorems in `LearningLean/Quantum/Norms.lean`, and `lake build` passes.

### Milestone 3: Time-ordered evolution in diamond norm (Appendix B)

Expose explicit `T_L(t,s)` and `T_L^-(t,s)` definitions in `LearningLean/Quantum/TimeOrderedMatrix.lean` by specializing the existing `TexpOfPicard` machinery. Prove Lemma 1 (equations B1 and B2) and Theorem 2 (equation B3) using the diamond norm lemmas. At the end of this milestone, `backward_evolution_bound_diamond_statement` and `timeOrdered_secondOrder_bound_diamond_statement` are theorems with proofs, and `AllClaims.lean` references them.

### Milestone 4: Algorithm error bounds and Pauli norm (Equations 6–9)

Introduce a concrete Pauli basis module (for example `LearningLean/Quantum/Pauli.lean`) that defines Pauli matrices, tensor products, and a decomposition of Lindbladians into Pauli terms. Replace `PauliDecomposition` with a concrete representation or add a concrete witness that connects coefficients to actual matrices. Prove the Pauli norm reduction bound and use it to turn equations (6)-(9) into theorems in `LearningLean/Quantum/Algorithm.lean`. At the end of this milestone, the algorithm error bounds are theorems with proofs, and the `*_statement` names now denote proved theorems.

### Milestone 5: Extensions and Remark 1

Formalize the time-dependent dissipator approximation in equation (10), the local noise decomposition in equation (12), and the ancilla-count argument in Remark 1 using Kraus ranks. Add any missing helper lemmas about Kraus rank and convex combinations in `LearningLean/Quantum/Channels.lean` or `LearningLean/Quantum/Extensions.lean`. At the end of this milestone, `timeDependent_extension`, `remark_ancilla_bound`, and `correlated_sampling_extension` are theorems with proofs.

### Milestone 6: Demonstrations and Section V equations

For the depolarizing, crosstalk, and 1/f dephasing examples, define the exact Hamiltonians, dissipators, and sampling procedures in `LearningLean/Quantum/Examples.lean`, then prove the norms and cost bounds corresponding to equations (13)-(29). Each example should explicitly link to the earlier definitions (Lindbladian form, Pauli norm, stochastic simulation) rather than introducing stand-alone statements. At the end of this milestone, all example statements are theorems, and `PAPER_GAPS.md` has no remaining open items.

## Concrete Steps

Run commands from `/Users/abhishekjain/my-git/learning-lean`.

1. Baseline gap check and build.

    rg -n "\bsorry\b|\baxiom\b" LearningLean
    lake build

   Expect no build errors but existing `sorry` hits in `LearningLean/Quantum/Stochastic.lean` until Milestone 1 is complete.

2. After each milestone, update the checklist and re-build.

    rg -n "\bsorry\b|\baxiom\b" LearningLean
    lake build

   Expect the grep to return fewer hits and the build to pass.

3. If mathlib gets corrupted, clean and retry.

    rm -rf .lake
    lake update
    lake build

## Validation and Acceptance

Final acceptance means the repository proves all paper claims, not just states them. A reviewer should be able to run `lake build` successfully and run `rg -n "\bsorry\b|\baxiom\b" LearningLean` with no matches. `LearningLean/Quantum/AllClaims.lean` must `#check` theorems for Definition 1, Lemma 1, Theorem 1, Theorem 2, Appendix A bound, Remark 1, and each demonstration. The `PAPER_GAPS.md` checklist must be fully marked as closed by removing or annotating every gap entry. Acceptance is observable when the above commands succeed and there are no remaining `_statement` placeholders without proofs.

## Idempotence and Recovery

All steps are additive and safe to re-run. If a proof attempt fails, keep the file compiling by backing out to the last successful state before proceeding. If `lake update` fails due to network or a corrupted checkout, delete `.lake/` and rerun once network access is available. Running `lake build` is always safe and should be used after every milestone.

## Artifacts and Notes

Example expected output after completion.

    $ rg -n "\bsorry\b|\baxiom\b" LearningLean
    (no output)

    $ lake build
    OK [..] Built LearningLean.Quantum.AllClaims
    Build completed successfully

## Interfaces and Dependencies

The following theorems and definitions must exist at the end of the plan, with the indicated paths, to match the paper and the checklist.

In `LearningLean/Quantum/Stochastic.lean`, define and prove.

    theorem expected_sampling_eq_stochasticAction : ...
    theorem expected_sampling_eq_channel : ...
    theorem repeated_sampling_eq_channel : ...

In `LearningLean/Quantum/Norms.lean`, define and prove.

    theorem diamondNorm_additive : ...
    theorem diamondNorm_submultiplicative : ...

In `LearningLean/Quantum/TimeOrderedMatrix.lean`, define and prove.

    def TL : ...
    def TL_inv : ...
    theorem backward_evolution_bound_diamond_statement : ...
    theorem timeOrdered_secondOrder_bound_diamond_statement : ...

In `LearningLean/Quantum/Algorithm.lean`, define and prove.

    theorem product_formula_error_bound_statement : ...
    theorem dissipator_error_bound_statement : ...
    theorem product_formula_pauli_bound_statement : ...
    theorem theorem1_query_complexity : ...

In `LearningLean/Quantum/Examples.lean`, define and prove.

    theorem depolarizing_example_statement : ...
    theorem crosstalk_example_statement : ...
    theorem oneOverF_dephasing_example_statement : ...

Plan change note (2026-01-09): Replaced the previous plan with a checklist-driven plan that targets the remaining gaps recorded in `PAPER_GAPS.md`, because the earlier plan marked items complete that still exist only as statements or contain `sorry`.
