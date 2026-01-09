import Mathlib

namespace LearningLean.Quantum

abbrev SuperOp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :=
  V →L[ℂ] V

def comm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A B : SuperOp V) : SuperOp V :=
  (A.comp B) - (B.comp A)

end LearningLean.Quantum
