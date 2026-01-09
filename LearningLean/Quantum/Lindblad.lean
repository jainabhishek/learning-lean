import Mathlib

import LearningLean.Quantum.Prelude
import LearningLean.Quantum.TimeOrdered

namespace LearningLean.Quantum

noncomputable section

open Set

abbrev leftEndpoint (s t : ℝ) (hs : s ≤ t) : Set.Icc s t :=
  ⟨s, ⟨le_rfl, hs⟩⟩

/-- Build Picard–Lindelöf data for a linear field on `[s,t]` from continuity and a uniform bound. -/
lemma linearField_isPicardLindelof_leftEndpoint
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {L : ℝ → SuperOp V} {s t : ℝ} (hs : s ≤ t)
    (x0 : SuperOp V) (a M : NNReal)
    (hM : ∀ u ∈ Set.Icc s t, ‖L u‖ ≤ M)
    (hL : ContinuousOn L (Set.Icc s t))
    (hmul : (M * (a + ‖x0‖₊)) * (t - s) ≤ a) :
    IsPicardLindelof (linearField L) (leftEndpoint s t hs) x0 a 0 (M * (a + ‖x0‖₊)) M := by
  have hmul' :
      (M * (a + ‖x0‖₊)) *
          max (t - (leftEndpoint s t hs : ℝ)) ((leftEndpoint s t hs : ℝ) - s) ≤ a := by
    simpa [leftEndpoint, sub_self, max_eq_left, sub_nonneg.mpr hs] using hmul
  exact
    linearField_isPicardLindelof_of_continuousOn (t0 := leftEndpoint s t hs)
      (L := L) (x0 := x0) (a := a) (M := M) hM hL hmul'

/-- Statement skeleton for the operator-norm analogue of Theorem 2, based on `TexpOfPicard`. -/
def timeOrdered_secondOrder_bound_opNorm_statement
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] : Prop :=
  ∀ (H : SuperOp V) (D : ℝ → SuperOp V) (s t : ℝ)
    (M Kcomm a Lbound Klip : NNReal) (hs : s ≤ t),
    (∀ u ∈ Set.Icc s t, ‖D u‖ ≤ M) →
    (∀ u ∈ Set.Icc s t, ‖comm H (D u)‖ ≤ Kcomm) →
    (‖H‖ / 2 + (M : ℝ)) * (t - s) ≤ 1 →
    (hfHD :
      IsPicardLindelof (linearField (fun u => H + D u)) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ V) a 0 Lbound Klip) →
    (hfD :
      IsPicardLindelof (linearField D) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ V) a 0 Lbound Klip) →
    (hfH :
      IsPicardLindelof (linearField (fun _ => H)) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ V) a 0 Lbound Klip) →
    ‖TexpOfPicard hfHD t -
        (TexpOfPicard hfH (s + (t - s) / 2)).comp
          ((TexpOfPicard hfD t).comp (TexpOfPicard hfH (s + (t - s) / 2)))‖ ≤
      (Kcomm : ℝ) / 3 * (‖H‖ / 2 + (M : ℝ)) * (t - s) ^ 3

/-- Continuity-based variant that constructs Picard–Lindelöf data via `linearField_isPicardLindelof_leftEndpoint`. -/
def timeOrdered_secondOrder_bound_opNorm_statement_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] : Prop :=
  ∀ (H : SuperOp V) (D : ℝ → SuperOp V) (s t : ℝ)
    (M Kcomm a Lbound Klip : NNReal) (hs : s ≤ t)
    (hD : ∀ u ∈ Set.Icc s t, ‖D u‖ ≤ M)
    (hHD : ∀ u ∈ Set.Icc s t, ‖H + D u‖ ≤ Lbound)
    (hComm : ∀ u ∈ Set.Icc s t, ‖comm H (D u)‖ ≤ Kcomm)
    (hH : ‖H‖ ≤ Lbound)
    (hSmall : (‖H‖ / 2 + (M : ℝ)) * (t - s) ≤ 1)
    (hDcont : ContinuousOn D (Set.Icc s t))
    (hHDcont : ContinuousOn (fun u => H + D u) (Set.Icc s t))
    (hmulD : (M * (a + ‖(ContinuousLinearMap.id ℂ V)‖₊)) * (t - s) ≤ a)
    (hmulHD : (Lbound * (a + ‖(ContinuousLinearMap.id ℂ V)‖₊)) * (t - s) ≤ a)
    (hmulH : (Lbound * (a + ‖(ContinuousLinearMap.id ℂ V)‖₊)) * (t - s) ≤ a),
    let hfHD :=
      linearField_isPicardLindelof_leftEndpoint (L := fun u => H + D u) (hs := hs)
        (x0 := ContinuousLinearMap.id ℂ V) (a := a) (M := Lbound) hHD hHDcont hmulHD
    let hfD :=
      linearField_isPicardLindelof_leftEndpoint (L := D) (hs := hs)
        (x0 := ContinuousLinearMap.id ℂ V) (a := a) (M := M) hD hDcont hmulD
    let hfH :=
      linearField_isPicardLindelof_leftEndpoint (L := fun _ => H) (hs := hs)
        (x0 := ContinuousLinearMap.id ℂ V) (a := a) (M := Lbound)
        (by
          intro u hu
          simpa using hH)
        (by
          simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => H) (Set.Icc s t)))
        hmulH
    ‖TexpOfPicard hfHD t -
        (TexpOfPicard hfH (s + (t - s) / 2)).comp
          ((TexpOfPicard hfD t).comp (TexpOfPicard hfH (s + (t - s) / 2)))‖ ≤
      (Kcomm : ℝ) / 3 * (‖H‖ / 2 + (M : ℝ)) * (t - s) ^ 3

lemma TexpOfPicard_hasDerivWithinAt_HD
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {H : SuperOp V} {D : ℝ → SuperOp V} {s t : ℝ} (hs : s ≤ t)
    {a Lbound Klip : NNReal}
    (hfHD :
      IsPicardLindelof (linearField (fun u => H + D u)) (leftEndpoint s t hs)
        (ContinuousLinearMap.id ℂ V) a 0 Lbound Klip) :
    ∀ u ∈ Set.Icc s t,
      HasDerivWithinAt (TexpOfPicard hfHD)
        (linearField (fun u => H + D u) u (TexpOfPicard hfHD u)) (Set.Icc s t) u := by
  simpa using (TexpOfPicard_hasDerivWithinAt (t0 := leftEndpoint s t hs)
    (x0 := ContinuousLinearMap.id ℂ V) (a := a) (L := Lbound) (K := Klip) hfHD)

end

end LearningLean.Quantum
