import Mathlib

import LearningLean.Quantum.TimeOrdered
import LearningLean.Quantum.Lindblad
import LearningLean.Quantum.LindbladMatrix
import LearningLean.Quantum.Continuous

namespace LearningLean.Quantum

abbrev MatSuperOp (d : Nat) := SuperOp (Mat d)

noncomputable abbrev MatLinearField {d : Nat} (L : ℝ → MatSuperOp d) :
    ℝ → MatSuperOp d → MatSuperOp d :=
  linearField (V := Mat d) L

noncomputable abbrev MatLinearFieldRight {d : Nat} (L : ℝ → MatSuperOp d) :
    ℝ → MatSuperOp d → MatSuperOp d :=
  linearFieldRight (V := Mat d) L

noncomputable abbrev MatBackwardLinearField {d : Nat} (L : ℝ → MatSuperOp d) :
    ℝ → MatSuperOp d → MatSuperOp d :=
  backwardLinearField (V := Mat d) L

noncomputable def hamiltonianFieldCLM {d : Nat} (H : Mat d) : ℝ → MatSuperOp d :=
  fun _ => hamiltonianCLM H

noncomputable def dissipatorFieldCLM {d : Nat} (Ls : ℝ → List (Mat d)) : ℝ → MatSuperOp d :=
  fun t => dissipatorCLM (Ls t)

noncomputable def liouvillianFieldCLM {d : Nat} (H : Mat d) (Ls : ℝ → List (Mat d)) :
    ℝ → MatSuperOp d :=
  fun t => liouvillianCLM H (Ls t)

-- Appendix B Lemma 1 (equations B1-B2) as a Lean statement.
def backward_evolution_bound_diamond_statement {d : Nat} : Prop :=
  ∀ (L : ℝ → MatSuperOp d) (s t : ℝ)
    (a Lbound Klip : NNReal) (hs : s ≤ t),
    (hf :
      IsPicardLindelof (MatLinearField L) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ (Mat d)) a 0 Lbound Klip) →
    (hb :
      IsPicardLindelof (MatBackwardLinearField L) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ (Mat d)) a 0 Lbound Klip) →
    (TexpOfPicard hf t).comp (TexpOfPicard hb t) = ContinuousLinearMap.id ℂ (Mat d) ∧
    (TexpOfPicard hb t).comp (TexpOfPicard hf t) = ContinuousLinearMap.id ℂ (Mat d) ∧
    diamondNormCLM (TexpOfPicard hb t) ≤
      Real.exp (∫ u in s..t, diamondNormCLM (L u))

-- Appendix B Theorem 2 (equation B3) as a Lean statement.
def timeOrdered_secondOrder_bound_diamond_statement {d : Nat} : Prop :=
  ∀ (H : MatSuperOp d) (D : ℝ → MatSuperOp d) (s t : ℝ)
    (M Kcomm a Lbound Klip : NNReal) (hs : s ≤ t),
    (∀ u ∈ Set.Icc s t, diamondNormCLM (D u) ≤ M) →
    (∀ u ∈ Set.Icc s t, diamondNormCLM (comm H (D u)) ≤ Kcomm) →
    (diamondNormCLM H / 2 + (M : ℝ)) * (t - s) ≤ 1 →
    (hfHD :
      IsPicardLindelof (MatLinearField (fun u => H + D u)) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ (Mat d)) a 0 Lbound Klip) →
    (hfD :
      IsPicardLindelof (MatLinearField D) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ (Mat d)) a 0 Lbound Klip) →
    (hfH :
      IsPicardLindelof (MatLinearField (fun _ => H)) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ (Mat d)) a 0 Lbound Klip) →
    diamondNormCLM (TexpOfPicard hfHD t -
        (TexpOfPicard hfH (s + (t - s) / 2)).comp
          ((TexpOfPicard hfD t).comp (TexpOfPicard hfH (s + (t - s) / 2)))) ≤
      (Kcomm : ℝ) / 3 * (diamondNormCLM H / 2 + (M : ℝ)) * (t - s) ^ 3

end LearningLean.Quantum
