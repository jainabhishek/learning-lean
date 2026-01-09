import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.States
import LearningLean.Quantum.Channels

open scoped ComplexOrder MatrixOrder

namespace LearningLean.Quantum

noncomputable def traceNorm {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) : Real :=
  Complex.re (Matrix.trace (CFC.sqrt (Matrix.conjTranspose A * A)))

lemma traceNorm_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) : 0 ≤ traceNorm A := by
  classical
  let B : Matrix n n Complex := CFC.sqrt (Matrix.conjTranspose A * A)
  have hposB : Matrix.PosSemidef B := by
    have hnonneg : (0 : Matrix n n Complex) ≤ B :=
      CFC.sqrt_nonneg (Matrix.conjTranspose A * A)
    simpa [Matrix.nonneg_iff_posSemidef] using hnonneg
  have hherm : Matrix.IsHermitian B := hposB.isHermitian
  have htrace : Matrix.trace B = ∑ i, (hherm.eigenvalues i : Complex) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hherm
  have hre : Complex.re (Matrix.trace B) = ∑ i, hherm.eigenvalues i := by
    classical
    simp [htrace]
  have hsum_nonneg : 0 ≤ ∑ i, hherm.eigenvalues i := by
    classical
    exact Fintype.sum_nonneg fun i => hposB.eigenvalues_nonneg i
  have hre_nonneg : 0 ≤ Complex.re (Matrix.trace B) := by
    simpa [hre] using hsum_nonneg
  simpa [traceNorm, B] using hre_nonneg

lemma traceNorm_zero {n : Type} [Fintype n] [DecidableEq n] :
    traceNorm (0 : Matrix n n Complex) = 0 := by
  simp [traceNorm]

lemma traceNorm_neg {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n Complex) :
    traceNorm (-A) = traceNorm A := by
  simp [traceNorm]
noncomputable def tensorIdFun {d dAnc : Nat} (phi : SuperOpMat d) :
    MatTensor d dAnc -> MatTensor d dAnc :=
  fun rho i j =>
    let a := i.2
    let b := j.2
    let block : Mat d := fun r c => rho (r, a) (c, b)
    let block' := phi block
    block' i.1 j.1

noncomputable def tensorId {d dAnc : Nat} (phi : SuperOpMat d) :
    MatTensor d dAnc →ₗ[Complex] MatTensor d dAnc :=
  { toFun := tensorIdFun phi
    map_add' := by
      intro x y
      ext i j
      let blockX : Mat d := fun r c => x (r, i.2) (c, j.2)
      let blockY : Mat d := fun r c => y (r, i.2) (c, j.2)
      have hblock :
          (fun r c => x (r, i.2) (c, j.2) + y (r, i.2) (c, j.2)) = blockX + blockY := by
        ext r c
        simp [blockX, blockY, Matrix.add_apply]
      have hphi : phi (blockX + blockY) = phi blockX + phi blockY :=
        phi.map_add blockX blockY
      have hphiEntry :
          phi (blockX + blockY) i.1 j.1 = (phi blockX + phi blockY) i.1 j.1 :=
        congrArg (fun m => m i.1 j.1) hphi
      calc
        phi (fun r c => (x + y) (r, i.2) (c, j.2)) i.1 j.1 =
            phi (blockX + blockY) i.1 j.1 := by
              simp [Matrix.add_apply, hblock]
        _ = (phi blockX + phi blockY) i.1 j.1 := hphiEntry
        _ =
            phi (fun r c => x (r, i.2) (c, j.2)) i.1 j.1 +
              phi (fun r c => y (r, i.2) (c, j.2)) i.1 j.1 := by
              simp [blockX, blockY, Matrix.add_apply]
    map_smul' := by
      intro c x
      ext i j
      let blockX : Mat d := fun r c_1 => x (r, i.2) (c_1, j.2)
      have hblock :
          (fun r c_1 => c * x (r, i.2) (c_1, j.2)) = c • blockX := by
        ext r c_1
        simp [blockX, Matrix.smul_apply]
      have hphi : phi (c • blockX) = c • phi blockX :=
        phi.map_smul c blockX
      have hphiEntry :
          phi (c • blockX) i.1 j.1 = (c • phi blockX) i.1 j.1 :=
        congrArg (fun m => m i.1 j.1) hphi
      calc
        phi (fun r c_1 => (c • x) (r, i.2) (c_1, j.2)) i.1 j.1 =
            phi (c • blockX) i.1 j.1 := by
              simp [Matrix.smul_apply, hblock]
        _ = (c • phi blockX) i.1 j.1 := hphiEntry
        _ = c • phi (fun r c_1 => x (r, i.2) (c_1, j.2)) i.1 j.1 := by
              simp [blockX, Matrix.smul_apply] }

noncomputable def diamondNorm {d : Nat} (phi : SuperOpMat d) : Real :=
  sSup { r : Real |
    Exists fun rho : DensityMatrixTensor d d =>
      r = traceNorm (tensorId (d := d) (dAnc := d) phi rho.val)
  }

lemma diamondNorm_nonneg {d : Nat} (phi : SuperOpMat d) : 0 ≤ diamondNorm phi := by
  refine Real.sSup_nonneg ?_
  intro r hr
  rcases hr with ⟨rho, rfl⟩
  simpa using traceNorm_nonneg (A := tensorId (d := d) (dAnc := d) phi rho.val)

lemma diamondNorm_zero {d : Nat} : diamondNorm (0 : SuperOpMat d) = 0 := by
  apply le_antisymm
  · refine Real.sSup_le ?_ ?_
    · intro r hr
      rcases hr with ⟨rho, rfl⟩
      have hzero :
          tensorIdFun (d := d) (dAnc := d) (0 : SuperOpMat d) rho.val = 0 := by
        ext i j
        simp [tensorIdFun]
      simp [tensorId, hzero, traceNorm_zero]
    · exact le_rfl
  · exact diamondNorm_nonneg (phi := (0 : SuperOpMat d))

structure PauliDecomposition (d : Nat) where
  L : SuperOpMat d
  s : Nat
  m : Nat
  beta0 : Fin s → Real
  beta : Fin m → Fin s → Real
  beta0_pos : ∀ k, 0 < beta0 k
  beta_pos : ∀ mu k, 0 < beta mu k

noncomputable def hamiltonianPauliNorm {d : Nat} (dec : PauliDecomposition d) : Real :=
  Finset.sum Finset.univ (fun k : Fin dec.s => dec.beta0 k)

noncomputable def pauliNorm {d : Nat} (dec : PauliDecomposition d) : Real :=
  hamiltonianPauliNorm dec +
    Finset.sum Finset.univ (fun mu : Fin dec.m =>
      (Finset.sum Finset.univ (fun k : Fin dec.s => dec.beta mu k)) ^ (2 : Nat))

-- Pauli norm reduction from the paper as a Lean statement.
def pauli_norm_reduction_statement {d : Nat} : Prop :=
  ∀ dec : PauliDecomposition d,
    diamondNorm dec.L ≤ 2 * pauliNorm dec

end LearningLean.Quantum
