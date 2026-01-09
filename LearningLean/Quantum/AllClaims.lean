import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.States
import LearningLean.Quantum.Channels
import LearningLean.Quantum.Norms
import LearningLean.Quantum.Continuous
import LearningLean.Quantum.Stochastic
import LearningLean.Quantum.AppendixA
import LearningLean.Quantum.TimeOrdered
import LearningLean.Quantum.Lindblad
import LearningLean.Quantum.LindbladMatrix
import LearningLean.Quantum.TimeOrderedMatrix
import LearningLean.Quantum.Algorithm
import LearningLean.Quantum.Extensions
import LearningLean.Quantum.Examples

namespace LearningLean.Quantum

-- Summary entry point for paper claim checks. Proofs will be added as the formalization progresses.

def allClaimsLoaded : Bool := true

-- Core paper claims
#check stochastically_simulatable
#check backward_evolution_bound_diamond_statement
#check timeOrdered_secondOrder_bound_diamond_statement
#check randomUnitaryApprox_bound_statement
#check pauli_norm_reduction_statement
#check product_formula_error_bound_statement
#check dissipator_error_bound_statement
#check product_formula_pauli_bound_statement
#check theorem1_query_complexity
#check theorem1_gate_complexity

-- Extensions
#check timeDependent_extension
#check remark_ancilla_bound
#check correlated_sampling_extension

-- Examples
#check depolarizing_example_statement
#check crosstalk_example_statement
#check oneOverF_dephasing_example_statement

end LearningLean.Quantum
