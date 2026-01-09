import Mathlib

import LearningLean.Quantum.Channels
import LearningLean.Quantum.Continuous
import LearningLean.Quantum.Norms

namespace LearningLean.Quantum

def compose {d : Nat} (f g : SuperOpMat d) : SuperOpMat d :=
  f.comp g

structure SimulationGadget (d : Nat) where
  K_delta_t : SuperOpMat d
  N_delta_t : SuperOpMat d

noncomputable def runGadget {d : Nat} (g : SimulationGadget d) : SuperOpMat d :=
  compose g.K_delta_t (compose g.N_delta_t g.K_delta_t)

noncomputable def runGadgetPow {d : Nat} (g : SimulationGadget d) : Nat → SuperOpMat d
  | 0 => LinearMap.id
  | n + 1 => compose (runGadget g) (runGadgetPow g n)

noncomputable def expSuperOp {d : Nat} (t : Real) (L : SuperOpMat d) : SuperOpMat d :=
  (NormedSpace.exp ℂ ((Complex.ofReal t) • L.toCLM)).toLM

noncomputable def commSuperOp {d : Nat} (A B : SuperOpMat d) : SuperOpMat d :=
  A.comp B - B.comp A

noncomputable def epsilonH {d : Nat} (delta_t : Real) (H K : SuperOpMat d) : Real :=
  diamondNorm (expSuperOp (delta_t / 2) H - K)

noncomputable def epsilonD {d : Nat} (delta_t : Real) (D N : SuperOpMat d) : Real :=
  diamondNorm (expSuperOp delta_t D - N)

-- Equation (6) in the paper as a Lean statement.
def product_formula_error_bound_statement {d : Nat} : Prop :=
  ∀ (H D K N : SuperOpMat d) (T delta_t : Real) (r : Nat),
    (diamondNorm H / 2 + diamondNorm D) * delta_t ≤ 1 →
    T = delta_t * (r : Real) →
    let g : SimulationGadget d := { K_delta_t := K, N_delta_t := N }
    diamondNorm (expSuperOp T (H + D) - runGadgetPow g r) ≤
      (diamondNorm (commSuperOp H D) / 3) *
          (diamondNorm H / 2 + diamondNorm D) * (r : Real) * delta_t ^ 3 +
        2 * (r : Real) * (epsilonH delta_t H K + epsilonD delta_t D N)

-- Equation (7) in the paper as a Lean statement.
def dissipator_error_bound_statement {d : Nat} : Prop :=
  ∀ (D N : SuperOpMat d) (delta_t c0 : Real),
    epsilonD delta_t D N ≤ c0 * (diamondNorm D * delta_t) ^ 3

-- Equation (8) in the paper as a Lean statement.
def product_formula_pauli_bound_statement {d : Nat} : Prop :=
  ∀ (H D K N : SuperOpMat d) (T delta_t : Real) (r : Nat) (c0 : Real)
    (decomp : PauliDecomposition d),
    decomp.L = H + D →
    (diamondNorm H / 2 + diamondNorm D) * delta_t ≤ 1 →
    epsilonD delta_t D N ≤ c0 * (diamondNorm D * delta_t) ^ 3 →
    diamondNorm (H + D) ≤ 2 * pauliNorm decomp →
    T = delta_t * (r : Real) →
    let g : SimulationGadget d := { K_delta_t := K, N_delta_t := N }
    diamondNorm (expSuperOp T (H + D) - runGadgetPow g r) ≤
      (8 / 3) * (r : Real) * (1 + 6 * c0) * (pauliNorm decomp * delta_t) ^ 3 +
        2 * (r : Real) * epsilonH delta_t H K

-- Soft-O placeholder for asymptotic bounds with suppressed polylog factors.
def softO (cost bound : Real) : Prop :=
  ∃ C : Real, 0 ≤ C ∧ cost ≤ C * bound

-- Theorem 1 query complexity (equation (9)) as a Lean statement.
def theorem1_query_complexity {d : Nat} : Prop :=
  ∀ (T epsilon c0 : Real) (decomp : PauliDecomposition d),
    0 < epsilon →
    ∃ r : Nat,
      softO (r : Real)
        (Real.sqrt ((1 + 6 * c0) / epsilon) *
          Real.sqrt ((pauliNorm decomp * T) ^ 3)) ∧
      ∃ epsilonH_val : Real,
        softO epsilonH_val (epsilon / (r : Real))

-- Gate complexity statement for the truncated Taylor series subroutine.
def theorem1_gate_complexity {d : Nat} : Prop :=
  ∀ (delta_t epsilonH_val : Real) (n : Nat) (decomp : PauliDecomposition d)
    (gate_sub gate_total : Real) (r : Nat),
    0 < delta_t →
    0 < epsilonH_val →
    softO gate_sub
      (delta_t * hamiltonianPauliNorm decomp * (decomp.s : Real) * (n : Real) *
        Real.log (delta_t * hamiltonianPauliNorm decomp / epsilonH_val)) →
    gate_total = (r : Real) * gate_sub

end LearningLean.Quantum
