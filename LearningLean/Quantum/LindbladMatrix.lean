import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.Channels
import LearningLean.Quantum.Continuous

namespace LearningLean.Quantum

noncomputable def commMat {d : Nat} (A B : Mat d) : Mat d :=
  A * B - B * A

noncomputable def commSuper {d : Nat} (A : Mat d) : SuperOpMat d :=
  leftMul A - rightMul A

noncomputable def hamiltonian {d : Nat} (H : Mat d) : SuperOpMat d :=
  (-Complex.I) • commSuper H

noncomputable def dissipatorTerm {d : Nat} (L : Mat d) : SuperOpMat d :=
  let LdagL := Matrix.conjTranspose L * L
  conjBy L - ((1 : Complex) / 2) • (leftMul LdagL + rightMul LdagL)

noncomputable def dissipator {d : Nat} (Ls : List (Mat d)) : SuperOpMat d :=
  (Ls.map dissipatorTerm).sum

noncomputable def liouvillian {d : Nat} (H : Mat d) (Ls : List (Mat d)) : SuperOpMat d :=
  hamiltonian H + dissipator Ls

noncomputable def hamiltonianCLM {d : Nat} (H : Mat d) : SuperOpMatCLM d :=
  (hamiltonian H).toCLM

noncomputable def dissipatorCLM {d : Nat} (Ls : List (Mat d)) : SuperOpMatCLM d :=
  (dissipator Ls).toCLM

noncomputable def liouvillianCLM {d : Nat} (H : Mat d) (Ls : List (Mat d)) : SuperOpMatCLM d :=
  (liouvillian H Ls).toCLM

end LearningLean.Quantum
