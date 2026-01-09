import Mathlib

import LearningLean.Quantum.Algorithm
import LearningLean.Quantum.Channels
import LearningLean.Quantum.Norms

namespace LearningLean.Quantum

noncomputable def supReal (f : Real → Real) : Real :=
  sSup (Set.range f)

noncomputable def supPauliNorm {d : Nat} (decomp : Real → PauliDecomposition d) : Real :=
  supReal (fun t => pauliNorm (decomp t))

noncomputable def supC0 (c0 : Real → Real) : Real :=
  supReal c0

-- Section IV.A: time-dependent dissipator extension of Theorem 1.
def timeDependent_extension {d : Nat} : Prop :=
  ∀ (L : Real → SuperOpMat d) (T epsilon : Real)
    (decomp : Real → PauliDecomposition d) (c0 : Real → Real),
    (∀ t, (decomp t).L = L t) →
    0 < epsilon →
    ∃ r : Nat,
      softO (r : Real)
        (Real.sqrt ((1 + 6 * supC0 c0) / epsilon) *
          Real.sqrt ((supPauliNorm decomp * T) ^ 3)) ∧
      ∃ epsilonH_val : Real,
        softO epsilonH_val (epsilon / (r : Real))

def krausRankLe {d : Nat} (E : Channel d) (k : Nat) : Prop :=
  ∃ ks : Kraus d, E.map = krausMap ks ∧ ks.length ≤ k

noncomputable def convexChannelMap {d : Nat} (lambdas : List Real)
    (channels : List (Channel d)) : SuperOpMat d :=
  (lambdas.zipWith (fun l ch => (Complex.ofReal l) • ch.map) channels).sum

-- Section IV.B: Remark 1 (ancilla bound) in terms of Kraus ranks.
def remark_ancilla_bound : Prop :=
  ∀ l : Nat, ∀ E : Channel (2 ^ l),
    ∃ lambdas : List Real, ∃ channels : List (Channel (2 ^ l)),
      (List.Forall (fun w => 0 ≤ w) lambdas) ∧
      lambdas.sum = 1 ∧
      lambdas.length = channels.length ∧
      E.map = convexChannelMap lambdas channels ∧
      List.Forall (fun ch => krausRankLe ch (2 ^ l)) channels

noncomputable def composeList {d : Nat} : List (SuperOpMat d) → SuperOpMat d
  | [] => LinearMap.id
  | f :: fs => f.comp (composeList fs)

noncomputable def correlatedChannelMap {d : Nat}
    (samples : List (Real × List (Channel d))) : SuperOpMat d :=
  (samples.map (fun s =>
      (Complex.ofReal s.1) • composeList (s.2.map (fun ch => ch.map)))).sum

-- Section IV.C: correlated sampling across time steps.
def correlated_sampling_extension {d : Nat} : Prop :=
  ∀ (samples : List (Real × List (Channel d))),
    (List.Forall (fun s => 0 ≤ s.1) samples) →
    (samples.map (fun s => s.1)).sum = 1 →
    ∃ E : Channel d, E.map = correlatedChannelMap samples

end LearningLean.Quantum
