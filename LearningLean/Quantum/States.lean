import Mathlib

import LearningLean.Quantum.Matrix

namespace LearningLean.Quantum

structure DensityMatrixIdx (n : Type) [Fintype n] [DecidableEq n] where
  val : Matrix n n Complex
  hermitian : Matrix.IsHermitian val
  posSemidef : PosSemidef val
  trace_one : Matrix.trace val = (1 : Complex)

abbrev DensityMatrix (d : Nat) := DensityMatrixIdx (Fin d)
abbrev DensityMatrixTensor (d dAnc : Nat) := DensityMatrixIdx (Prod (Fin d) (Fin dAnc))

def DensityMatrixIdx.toMat {n : Type} [Fintype n] [DecidableEq n] (rho : DensityMatrixIdx n) :
    Matrix n n Complex :=
  rho.val

instance {n : Type} [Fintype n] [DecidableEq n] : CoeTC (DensityMatrixIdx n) (Matrix n n Complex) where
  coe rho := rho.val

@[simp] lemma DensityMatrixIdx.coe_val {n : Type} [Fintype n] [DecidableEq n]
    (rho : DensityMatrixIdx n) : ((rho : Matrix n n Complex)) = rho.val := rfl

end LearningLean.Quantum
