import Mathlib

open scoped ComplexOrder

namespace LearningLean.Quantum

abbrev Mat (d : Nat) := Matrix (Fin d) (Fin d) Complex
abbrev MatTensor (d dAnc : Nat) := Matrix (Prod (Fin d) (Fin dAnc)) (Prod (Fin d) (Fin dAnc)) Complex

abbrev HermitianMat (d : Nat) := { A : Mat d // Matrix.IsHermitian A }
abbrev PSDMat (d : Nat) := { A : Mat d // Matrix.PosSemidef A }

abbrev adjoint {d : Nat} (A : Mat d) : Mat d := Matrix.conjTranspose A
noncomputable def trace {d : Nat} (A : Mat d) : Complex := Matrix.trace A

abbrev ident (d : Nat) : Mat d := 1

abbrev kron {d dAnc : Nat} (A : Mat d) (B : Mat dAnc) : MatTensor d dAnc :=
  Matrix.kronecker A B

abbrev PosSemidef {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n Complex) : Prop :=
  Matrix.PosSemidef A

noncomputable instance (d : Nat) : NormedAddCommGroup (Mat d) := by
  classical
  simpa [Mat] using
    (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := Complex))

noncomputable instance (d : Nat) : NormedSpace Complex (Mat d) := by
  classical
  simpa [Mat] using
    (Matrix.frobeniusNormedSpace (m := Fin d) (n := Fin d) (R := Complex) (α := Complex))

end LearningLean.Quantum
