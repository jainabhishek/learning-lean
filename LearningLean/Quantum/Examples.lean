import Mathlib

import LearningLean.Quantum.Algorithm
import LearningLean.Quantum.AppendixA
import LearningLean.Quantum.Extensions
import LearningLean.Quantum.LindbladMatrix
import LearningLean.Quantum.Stochastic

namespace LearningLean.Quantum

structure ExampleStatement (d : Nat) where
  description : String

def qubitDim (n : Nat) : Nat :=
  2 ^ n

-- Section V.A: depolarizing dissipation (global and local).
def globalDepolarizingJumps (n : Nat) (gamma : Real)
    (jumps : List (UnitaryJump (qubitDim n))) : Prop :=
  jumps.length = 4 ^ n - 1 ∧
  (∀ jump ∈ jumps, jumpWeight jump = gamma / ((4 : Real) ^ n))

def globalDepolarizingDissipator (n : Nat) (gamma : Real) (D : SuperOpMat (qubitDim n)) : Prop :=
  ∃ jumps, globalDepolarizingJumps n gamma jumps ∧ D = unitaryJumpDissipator jumps

def global_depolarizing_pauli_norm_statement {n : Nat} : Prop :=
  ∀ (decomp : PauliDecomposition (qubitDim n)) (gamma : Real),
    decomp.m = 4 ^ n - 1 →
    (∀ mu : Fin decomp.m,
      (Finset.sum Finset.univ (fun k : Fin decomp.s => decomp.beta mu k)) =
        Real.sqrt (gamma / ((4 : Real) ^ n))) →
    pauliNorm decomp =
      hamiltonianPauliNorm decomp + (1 - 1 / ((4 : Real) ^ n)) * gamma

def global_depolarizing_example_statement {n : Nat} : Prop :=
  ∀ (H D : SuperOpMat (qubitDim n)) (T epsilon gamma : Real)
    (decomp : PauliDecomposition (qubitDim n)),
    globalDepolarizingDissipator n gamma D →
    decomp.L = H + D →
    0 < T →
    0 < epsilon →
    pauliNorm decomp =
      hamiltonianPauliNorm decomp + (1 - 1 / ((4 : Real) ^ n)) * gamma →
    ∃ r : Nat,
      softO (r : Real)
        (Real.sqrt (1 / epsilon) *
          Real.sqrt (((hamiltonianPauliNorm decomp + (1 - 1 / ((4 : Real) ^ n)) * gamma) * T) ^ 3)) ∧
      ∃ gate_total : Real, softO gate_total ((n : Real) * (r : Real)) ∧
        ∃ ancilla : Real, softO ancilla (Real.log (T / epsilon))

def localDepolarizingJumps (n : Nat) (gamma : Real)
    (jumps : List (UnitaryJump (qubitDim n))) : Prop :=
  jumps.length = 3 * n ∧
  (∀ jump ∈ jumps, jumpWeight jump = gamma / 4)

def localDepolarizingDissipator (n : Nat) (gamma : Real) (D : SuperOpMat (qubitDim n)) : Prop :=
  ∃ jumps, localDepolarizingJumps n gamma jumps ∧ D = unitaryJumpDissipator jumps

def local_depolarizing_example_statement {n : Nat} : Prop :=
  ∀ (H D : SuperOpMat (qubitDim n)) (T epsilon gamma : Real)
    (decomp : PauliDecomposition (qubitDim n)),
    localDepolarizingDissipator n gamma D →
    decomp.L = H + D →
    0 < T →
    0 < epsilon →
    pauliNorm decomp =
      hamiltonianPauliNorm decomp + (n : Real) * gamma / 4 →
    ∃ r : Nat,
      softO (r : Real)
        (Real.sqrt (1 / epsilon) *
          Real.sqrt (((hamiltonianPauliNorm decomp + (n : Real) * gamma / 4) * T) ^ 3)) ∧
      ∃ gate_total : Real, softO gate_total ((n : Real) * (r : Real))

def depolarizing_example_statement {n : Nat} : Prop :=
  global_depolarizing_example_statement (n := n) ∧
    local_depolarizing_example_statement (n := n)

-- Section V.B: ZZ crosstalk on two superconducting transmons.
def crosstalk_pauli_norm_statement : Prop :=
  ∀ (decomp : PauliDecomposition (qubitDim 2))
    (omega1 omega2 J gamma1 gamma2 gamma3 : Real),
    hamiltonianPauliNorm decomp = omega1 / 2 + omega2 / 2 + J →
    pauliNorm decomp =
      hamiltonianPauliNorm decomp + (gamma1 + gamma2 + gamma3)

def crosstalk_example_statement : Prop :=
  ∀ (H D : SuperOpMat (qubitDim 2)) (T epsilon : Real)
    (omega1 omega2 J gamma1 gamma2 gamma3 : Real)
    (decomp : PauliDecomposition (qubitDim 2)),
    decomp.L = H + D →
    0 < T →
    0 < epsilon →
    hamiltonianPauliNorm decomp = omega1 / 2 + omega2 / 2 + J →
    pauliNorm decomp =
      hamiltonianPauliNorm decomp + (gamma1 + gamma2 + gamma3) →
    ∃ r : Nat,
      softO (r : Real)
        (Real.sqrt (1 / epsilon) *
          Real.sqrt (((omega1 / 2 + omega2 / 2 + J + gamma1 + gamma2 + gamma3) * T) ^ 3)) ∧
      ∃ gate_total : Real, softO gate_total (r : Real)

-- Section V.C: 1/f dephasing and correlated sampling.
noncomputable def deltaT (T : Real) (N : Nat) : Real :=
  T / (N : Real)

noncomputable def timeGrid (T : Real) (N : Nat) (k : Nat) : Real :=
  (k : Real) * deltaT T N

noncomputable def omega (T : Real) (m : Nat) : Real :=
  2 * Real.pi * (m : Real) / T

noncomputable def oneOverFWeight (T : Real) (X Y : Nat → Real) (m : Nat) : Complex :=
  let w := omega T m
  (Complex.ofReal (Real.sqrt (1 / (2 * |w|)))) *
    (Complex.ofReal (X m) + Complex.I * Complex.ofReal (Y m))

def oneOverFConjugateSymm (N : Nat) (weights : Nat → Complex) : Prop :=
  ∀ m, m < N → m ≠ 0 → weights (N - m) = star (weights m)

noncomputable def oneOverFSample (T : Real) (N : Nat) (weights : Nat → Complex) (k : Nat) : Complex :=
  (Complex.ofReal (1 / Real.sqrt (N : Real))) *
    (Finset.sum (Finset.range N) (fun m =>
      weights m *
        Complex.exp (-Complex.I * (Complex.ofReal (omega T m * timeGrid T N k)))))

noncomputable def oneOverFRealSample (T : Real) (N : Nat) (weights : Nat → Complex) (k : Nat) : Real :=
  Complex.re (oneOverFSample T N weights k)

noncomputable def oneOverFRate (T : Real) (N : Nat) (weights : Nat → Complex) (k : Nat) : Real :=
  |oneOverFRealSample T N weights k|

def hasOneOverFSpectrum (T : Real) (N : Nat) (weights : Nat → Complex) : Prop :=
  ∀ m, m < N → m ≠ 0 →
    ‖weights m‖ ^ 2 = 1 / (2 * |omega T m|)

def oneOverF_sampling_statement : Prop :=
  ∀ (T : Real) (N : Nat) (X Y : Nat → Real),
    0 < T →
    0 < (N : Real) →
    let weights := fun m => oneOverFWeight T X Y m
    oneOverFConjugateSymm N weights →
    hasOneOverFSpectrum T N weights

def dephasingProbability (gamma delta_t : Real) : Real :=
  gamma * delta_t - gamma * delta_t ^ 2

noncomputable def dephasingDissipator {d : Nat} (gamma : Real) (Z : UnitaryMat d) : SuperOpMat d :=
  (Complex.ofReal (gamma / 2)) • (conjBy Z.val - (LinearMap.id : SuperOpMat d))

noncomputable def dephasingOracle {d : Nat} (p : Real) (Z : UnitaryMat d) : SuperOpMat d :=
  (Complex.ofReal (1 - p)) • (LinearMap.id : SuperOpMat d) +
    (Complex.ofReal p) • conjBy Z.val

def oneOverF_dissipative_taylor_statement {d : Nat} : Prop :=
  ∀ (gamma delta_t : Real) (Z : UnitaryMat d),
    let D := dephasingDissipator gamma Z
    let p := dephasingProbability gamma delta_t
    let N := dephasingOracle p Z
    ∃ c : Real, diamondNorm (expSuperOp delta_t D - N) ≤ c * delta_t ^ 3

def oneOverF_gate_cost_statement {n : Nat} : Prop :=
  ∀ (T : Real) (r : Nat) (gate_total : Real),
    0 < T →
    softO gate_total ((r : Real) * (n : Real))

def oneOverF_dephasing_example_statement {n : Nat} : Prop :=
  oneOverF_sampling_statement ∧
    correlated_sampling_extension (d := qubitDim n) ∧
    oneOverF_dissipative_taylor_statement (d := qubitDim n) ∧
    oneOverF_gate_cost_statement (n := n)

end LearningLean.Quantum
