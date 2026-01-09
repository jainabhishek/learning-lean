# Repository Guidelines

## Project Structure & Module Organization

`LearningLean/` is the Lean 4 library root. Quantum formalization lives in `LearningLean/Quantum/` (e.g., `Matrix.lean`, `Norms.lean`, `Algorithm.lean`, `Examples.lean`). `LearningLean.lean` is the library entry point that imports all modules. `Main.lean` is a small executable used for a lightweight build. The paper sources are `PhysRevResearch.7.023076.txt` and `.pdf`. Planning and tracking files are `EXECPLAN.md`, `PAPER_GAPS.md`, and `PLANS.md`.

## Build, Test, and Development Commands

- `lake build` — build the full library and surface Lean errors.
- `lake exe learning-lean` — run the minimal executable (sanity check).
- `rg -n "\\bsorry\\b|\\baxiom\\b" LearningLean` — find proof gaps.
- `lake update` — refresh dependencies if mathlib is corrupted (only when needed).

## Coding Style & Naming Conventions

Use Lean 4 style with two-space indentation and no tabs. Prefer `snake_case` for defs/lemmas that mirror paper statements (e.g., `product_formula_error_bound_statement`) and `PascalCase` for structures (`DensityMatrix`, `SimulationGadget`). Keep theorem names stable once referenced in `LearningLean/Quantum/AllClaims.lean`. Use brief comments to note paper equation numbers (e.g., “Equation (6)”); avoid verbose commentary.

## Testing Guidelines

This repo uses compilation as the test suite. Add `#check` lines in `LearningLean/Quantum/AllClaims.lean` for new theorems and ensure `lake build` succeeds. For formalization work, keep `rg -n "\\bsorry\\b|\\baxiom\\b"` output empty at completion.

## Commit & Pull Request Guidelines

History suggests short, conventional messages (e.g., `docs: ...`). Use concise, scoped subjects when possible. PRs should include: a brief summary, linked issue/plan (if any), `lake build` result, and any updates to `PAPER_GAPS.md` or `EXECPLAN.md` when closing claims.

## Planning & Formalization Workflow

Large changes should follow `EXECPLAN.md` and the rules in `PLANS.md`. Keep `PAPER_GAPS.md` in sync with any closed or reopened gaps so reviewers can confirm completeness quickly.
