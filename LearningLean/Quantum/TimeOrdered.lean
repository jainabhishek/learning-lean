import Mathlib

import LearningLean.Quantum.Prelude

namespace LearningLean.Quantum

universe u

class TimeOrderedEvolution (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] : Type (u + 1) where
  Texp : (ℝ → SuperOp V) → ℝ → ℝ → SuperOp V

noncomputable def compLeftCLM {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : SuperOp V) :
    SuperOp V →L[ℂ] SuperOp V :=
  ContinuousLinearMap.compL ℂ V V V A

noncomputable def compRightCLM {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : SuperOp V) :
    SuperOp V →L[ℂ] SuperOp V :=
  (ContinuousLinearMap.compL ℂ V V V).flip A

noncomputable def linearField {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (L : ℝ → SuperOp V) :
    ℝ → SuperOp V → SuperOp V :=
  fun t U => compLeftCLM (L t) U

noncomputable def linearFieldRight {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (L : ℝ → SuperOp V) :
    ℝ → SuperOp V → SuperOp V :=
  fun t U => compRightCLM (L t) U

noncomputable def backwardLinearField {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : ℝ → SuperOp V) :
    ℝ → SuperOp V → SuperOp V :=
  fun t U => - linearFieldRight L t U

lemma linearField_lipschitz {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : ℝ → SuperOp V) (t : ℝ) :
    LipschitzWith ‖compLeftCLM (L t)‖₊ (linearField L t) :=
  (compLeftCLM (L t)).lipschitz

lemma norm_compLeftCLM_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : SuperOp V) : ‖compLeftCLM A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (f := compLeftCLM A) (M := ‖A‖) (norm_nonneg _) ?_
  intro B
  simpa [compLeftCLM] using (ContinuousLinearMap.opNorm_comp_le (h := A) (f := B))

lemma linearField_norm_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : ℝ → SuperOp V) (t : ℝ) (U : SuperOp V) :
    ‖linearField L t U‖ ≤ ‖L t‖ * ‖U‖ := by
  have h := (ContinuousLinearMap.le_opNorm (compLeftCLM (L t)) U)
  have h' : ‖compLeftCLM (L t)‖ ≤ ‖L t‖ := norm_compLeftCLM_le (A := L t)
  exact h.trans (mul_le_mul_of_nonneg_right h' (norm_nonneg _))

section LinearFieldPicard

open Set Metric

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {tmin tmax : ℝ} (t0 : Set.Icc tmin tmax)
variable (L : ℝ → SuperOp V) (x0 : SuperOp V) (a M : NNReal)

lemma continuous_compLeftCLM : Continuous (compLeftCLM (V := V)) := by
  simpa [compLeftCLM] using (ContinuousLinearMap.compL ℂ V V V).continuous

lemma linearField_continuousOn_of_continuousOn
    {s : Set ℝ} (hL : ContinuousOn L s) (x : SuperOp V) :
    ContinuousOn (fun t => linearField L t x) s := by
  have hcomp : ContinuousOn (fun t => compLeftCLM (V := V) (L t)) s :=
    (continuous_compLeftCLM (V := V)).comp_continuousOn hL
  have hx : ContinuousOn (fun _ : ℝ => x) s := continuousOn_const
  simpa [linearField] using (ContinuousOn.clm_apply hcomp hx)

lemma linearField_isPicardLindelof
    (hM : ∀ t ∈ Set.Icc tmin tmax, ‖L t‖ ≤ M)
    (hcont :
      ∀ x ∈ closedBall x0 a, ContinuousOn (fun t => linearField L t x) (Set.Icc tmin tmax))
    (hmul : (M * (a + ‖x0‖₊)) * max (tmax - t0) (t0 - tmin) ≤ a) :
    IsPicardLindelof (linearField L) t0 x0 a 0 (M * (a + ‖x0‖₊)) M := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := hcont
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t ht
    have hLip : LipschitzWith ‖compLeftCLM (L t)‖₊ (linearField L t) := linearField_lipschitz L t
    have hLip_le : ‖compLeftCLM (L t)‖₊ ≤ M := by
      have hreal : ‖compLeftCLM (L t)‖ ≤ (M : ℝ) :=
        (norm_compLeftCLM_le (A := L t)).trans (hM t ht)
      exact_mod_cast hreal
    exact (hLip.weaken hLip_le).lipschitzOnWith
  · intro t ht x hx
    have hxball : ‖x - x0‖ ≤ (a : ℝ) := by
      simpa [dist_eq_norm] using (mem_closedBall.1 hx)
    have hxnorm : ‖x‖ ≤ (a : ℝ) + ‖x0‖ := by
      calc
        ‖x‖ = ‖x - x0 + x0‖ := by simp [sub_add_cancel]
        _ ≤ ‖x - x0‖ + ‖x0‖ := norm_add_le _ _
        _ ≤ (a : ℝ) + ‖x0‖ := by gcongr
    have hLt : ‖L t‖ ≤ (M : ℝ) := hM t ht
    have hmul' : ‖L t‖ * ‖x‖ ≤ (M : ℝ) * ((a : ℝ) + ‖x0‖) :=
      mul_le_mul hLt hxnorm (norm_nonneg _) (by exact_mod_cast (zero_le M))
    have hbound : ‖linearField L t x‖ ≤ (M : ℝ) * ((a : ℝ) + ‖x0‖) :=
      (linearField_norm_le L t x).trans hmul'
    simpa [NNReal.coe_add, coe_nnnorm] using hbound
  · simpa using hmul

lemma linearField_isPicardLindelof_of_continuousOn
    (hM : ∀ t ∈ Set.Icc tmin tmax, ‖L t‖ ≤ M)
    (hL : ContinuousOn L (Set.Icc tmin tmax))
    (hmul : (M * (a + ‖x0‖₊)) * max (tmax - t0) (t0 - tmin) ≤ a) :
    IsPicardLindelof (linearField L) t0 x0 a 0 (M * (a + ‖x0‖₊)) M := by
  refine linearField_isPicardLindelof (t0 := t0) (L := L) (x0 := x0) (a := a) (M := M) hM ?_ hmul
  intro x hx
  exact linearField_continuousOn_of_continuousOn (L := L) (s := Set.Icc tmin tmax) hL x

end LinearFieldPicard

section Picard

open Set

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E → E} {tmin tmax : ℝ} {t0 : Set.Icc tmin tmax} {x0 : E}
variable {a L K : NNReal}

noncomputable def TexpOfPicard (hf : IsPicardLindelof f t0 x0 a 0 L K) : ℝ → E :=
  Classical.choose (IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf)

lemma TexpOfPicard_initial (hf : IsPicardLindelof f t0 x0 a 0 L K) :
    TexpOfPicard hf (t0 : ℝ) = x0 := by
  simpa [TexpOfPicard] using
    (Classical.choose_spec (IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf)).1

lemma TexpOfPicard_hasDerivWithinAt (hf : IsPicardLindelof f t0 x0 a 0 L K) :
    ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt (TexpOfPicard hf) (f t (TexpOfPicard hf t)) (Set.Icc tmin tmax) t := by
  simpa [TexpOfPicard] using
    (Classical.choose_spec (IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hf)).2

end Picard

section Gronwall

open Set

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {tmin tmax : ℝ} {t0 : Set.Icc tmin tmax}
variable {L : ℝ → SuperOp V} {x0 : SuperOp V}
variable {a Lbound K M : NNReal}

lemma TexpOfPicard_norm_le_gronwall
    (hf : IsPicardLindelof (linearField L) t0 x0 a 0 Lbound K)
    (hM : ∀ t ∈ Set.Icc tmin tmax, ‖L t‖ ≤ M) :
    ∀ t ∈ Set.Icc (t0 : ℝ) tmax,
      ‖TexpOfPicard hf t‖ ≤ gronwallBound ‖x0‖ (M : ℝ) 0 (t - t0) := by
  intro t ht
  have hderiv := TexpOfPicard_hasDerivWithinAt (t0 := t0) (x0 := x0) (a := a) (L := Lbound) (K := K) hf
  have ht0 : tmin ≤ (t0 : ℝ) := t0.property.1
  have hsubset : Set.Icc (t0 : ℝ) tmax ⊆ Set.Icc tmin tmax := by
    intro x hx
    exact ⟨le_trans ht0 hx.1, hx.2⟩
  have hcont : ContinuousOn (TexpOfPicard hf) (Set.Icc (t0 : ℝ) tmax) := by
    intro x hx
    have hx' : x ∈ Set.Icc tmin tmax := hsubset hx
    exact (hderiv x hx').continuousWithinAt.mono hsubset
  have hderivRight :
      ∀ x ∈ Set.Ico (t0 : ℝ) tmax,
        HasDerivWithinAt (TexpOfPicard hf)
          (linearField L x (TexpOfPicard hf x)) (Set.Ici x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc tmin tmax := hsubset (Ico_subset_Icc_self hx)
    have hx'' : x ∈ Set.Ico tmin tmax := ⟨le_trans ht0 hx.1, hx.2⟩
    exact (hderiv x hx').mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx'')
  have hbound :
      ∀ x ∈ Set.Ico (t0 : ℝ) tmax,
        ‖linearField L x (TexpOfPicard hf x)‖ ≤ (M : ℝ) * ‖TexpOfPicard hf x‖ := by
    intro x hx
    have hx' : x ∈ Set.Icc tmin tmax := hsubset (Ico_subset_Icc_self hx)
    have hLt : ‖L x‖ ≤ (M : ℝ) := hM x hx'
    have hmul := linearField_norm_le L x (TexpOfPicard hf x)
    exact hmul.trans (mul_le_mul_of_nonneg_right hLt (norm_nonneg _))
  have ha : ‖TexpOfPicard hf (t0 : ℝ)‖ ≤ ‖x0‖ := by
    simp [TexpOfPicard_initial (t0 := t0) (x0 := x0) (a := a) (L := Lbound) (K := K) hf]
  have hbound' :
      ∀ x ∈ Set.Ico (t0 : ℝ) tmax,
        ‖linearField L x (TexpOfPicard hf x)‖ ≤ (M : ℝ) * ‖TexpOfPicard hf x‖ + 0 := by
    intro x hx
    simpa [add_zero] using (hbound x hx)
  exact
    norm_le_gronwallBound_of_norm_deriv_right_le hcont hderivRight ha hbound' t ht

end Gronwall

end LearningLean.Quantum
