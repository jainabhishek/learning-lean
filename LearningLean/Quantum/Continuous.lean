import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.Channels
import LearningLean.Quantum.Norms

namespace LearningLean.Quantum

abbrev SuperOpMatCLM (d : Nat) := Mat d →L[Complex] Mat d

noncomputable def SuperOpMat.toCLM {d : Nat} (phi : SuperOpMat d) : SuperOpMatCLM d :=
  LinearMap.toContinuousLinearMap phi

@[simp]
lemma SuperOpMat.toCLM_apply {d : Nat} (phi : SuperOpMat d) (x : Mat d) :
    phi.toCLM x = phi x := by
  rfl

abbrev SuperOpMatCLM.toLM {d : Nat} (phi : SuperOpMatCLM d) : SuperOpMat d :=
  phi.toLinearMap

@[simp]
lemma SuperOpMatCLM.toLM_apply {d : Nat} (phi : SuperOpMatCLM d) (x : Mat d) :
    phi.toLM x = phi x := by
  rfl

abbrev MatTensorCLM (d dAnc : Nat) := MatTensor d dAnc →L[Complex] MatTensor d dAnc

noncomputable def tensorIdCLM {d dAnc : Nat} (phi : SuperOpMat d) : MatTensorCLM d dAnc :=
  LinearMap.toContinuousLinearMap (tensorId (d := d) (dAnc := dAnc) phi)

@[simp]
lemma tensorIdCLM_apply {d dAnc : Nat} (phi : SuperOpMat d) (x : MatTensor d dAnc) :
    tensorIdCLM (d := d) (dAnc := dAnc) phi x = tensorId (d := d) (dAnc := dAnc) phi x := by
  rfl

noncomputable def diamondNormCLM {d : Nat} (phi : SuperOpMatCLM d) : Real :=
  diamondNorm (phi.toLM)

lemma diamondNormCLM_nonneg {d : Nat} (phi : SuperOpMatCLM d) : 0 ≤ diamondNormCLM phi := by
  simpa [diamondNormCLM] using diamondNorm_nonneg (phi := phi.toLM)

lemma diamondNormCLM_zero {d : Nat} : diamondNormCLM (0 : SuperOpMatCLM d) = 0 := by
  simpa [diamondNormCLM] using (diamondNorm_zero (d := d))

end LearningLean.Quantum
