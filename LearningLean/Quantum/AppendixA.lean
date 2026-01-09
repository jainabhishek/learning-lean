import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.Channels
import LearningLean.Quantum.Norms
import LearningLean.Quantum.Continuous
import LearningLean.Quantum.Stochastic

namespace LearningLean.Quantum

structure UnitaryJump (d : Nat) where
  coeff : Complex
  unitary : UnitaryMat d

def jumpWeight {d : Nat} (jump : UnitaryJump d) : Real :=
  Complex.normSq jump.coeff

def jumpWeightSum {d : Nat} (jumps : List (UnitaryJump d)) : Real :=
  (jumps.map jumpWeight).sum

noncomputable def randomUnitaryMap {d : Nat} (jumps : List (UnitaryJump d)) : SuperOpMat d :=
  (jumps.map (fun jump =>
      (Complex.ofReal (jumpWeight jump)) • conjBy jump.unitary.val)).sum

-- In Appendix A, the dissipator with unitary jump operators reduces to D = R - a I.
noncomputable def unitaryJumpDissipator {d : Nat} (jumps : List (UnitaryJump d)) : SuperOpMat d :=
  randomUnitaryMap jumps -
    (Complex.ofReal (jumpWeightSum jumps)) • (LinearMap.id : SuperOpMat d)

noncomputable def unitaryJumpDissipatorCLM {d : Nat} (jumps : List (UnitaryJump d)) :
    SuperOpMatCLM d :=
  (unitaryJumpDissipator jumps).toCLM

noncomputable def superOpPow {d : Nat} (R : SuperOpMat d) : Nat → SuperOpMat d
  | 0 => LinearMap.id
  | k + 1 => R.comp (superOpPow R k)

noncomputable def randomUnitarySeries {d : Nat} (delta : Real) (R : SuperOpMat d) (K : Nat) :
    SuperOpMat d :=
  Finset.sum (Finset.range (K + 1)) (fun k =>
    (Complex.ofReal (delta ^ k / (Nat.factorial k : Real))) • superOpPow R k)

noncomputable def randomUnitaryApproxCLM {d : Nat} (delta a : Real) (R : SuperOpMat d) (K : Nat) :
    SuperOpMatCLM d :=
  (Complex.ofReal (Real.exp (-a * delta))) • (randomUnitarySeries delta R K).toCLM

-- Appendix A bound (equation A1 in the paper) as a Lean statement.
def randomUnitaryApprox_bound_statement (d : Nat) : Prop :=
  ∀ (delta : Real) (K : Nat) (jumps : List (UnitaryJump d)) (c : Real),
    let R := randomUnitaryMap jumps
    let a := jumpWeightSum jumps
    delta * diamondNorm R ≤ 1 →
    diamondNormCLM
        (NormedSpace.exp ℂ ((Complex.ofReal delta) • unitaryJumpDissipatorCLM jumps) -
          randomUnitaryApproxCLM delta a R K)
      ≤ c * Real.exp (-a * delta) * (delta * diamondNorm R)^(K + 1) /
          (Nat.factorial (K + 1) : Real)

end LearningLean.Quantum
