import Mathlib
import Mathlib.Algebra.Algebra.Bilinear

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.States

namespace LearningLean.Quantum

abbrev SuperOpMat (d : Nat) := Mat d →ₗ[Complex] Mat d
abbrev Kraus (d : Nat) := List (Mat d)

noncomputable def leftMul {d : Nat} (A : Mat d) : SuperOpMat d :=
  LinearMap.mulLeft Complex A

noncomputable def rightMul {d : Nat} (A : Mat d) : SuperOpMat d :=
  LinearMap.mulRight Complex A

noncomputable def conjBy {d : Nat} (A : Mat d) : SuperOpMat d :=
  (leftMul A).comp (rightMul (Matrix.conjTranspose A))

noncomputable def krausMap {d : Nat} (ks : Kraus d) : SuperOpMat d :=
  (ks.map conjBy).sum

noncomputable def krausTracePreserving {d : Nat} (ks : Kraus d) : Prop :=
  (ks.map fun k => Matrix.conjTranspose k * k).sum = (1 : Mat d)

noncomputable def CPTP {d : Nat} (phi : SuperOpMat d) : Prop :=
  Exists fun ks => And (phi = krausMap ks) (krausTracePreserving ks)

structure Channel (d : Nat) where
  map : SuperOpMat d
  cptp : CPTP map

abbrev Channel.apply {d : Nat} (E : Channel d) (rho : Mat d) : Mat d :=
  E.map rho

abbrev Channel.applyDensity {d : Nat} (E : Channel d) (rho : DensityMatrix d) : Mat d :=
  E.map rho.val

lemma cptp_of_kraus {d : Nat} (ks : Kraus d) (hks : krausTracePreserving ks) :
    CPTP (krausMap ks) :=
  ⟨ks, rfl, hks⟩

noncomputable def channel_of_kraus {d : Nat} (ks : Kraus d) (hks : krausTracePreserving ks) :
    Channel d :=
  ⟨krausMap ks, cptp_of_kraus ks hks⟩

end LearningLean.Quantum
