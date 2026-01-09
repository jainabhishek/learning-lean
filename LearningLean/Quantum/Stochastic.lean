import Mathlib

import LearningLean.Quantum.Matrix
import LearningLean.Quantum.States
import LearningLean.Quantum.Channels

namespace LearningLean.Quantum

structure UnitaryMat (d : Nat) where
  val : Mat d
  unitary_left : Matrix.conjTranspose val * val = (1 : Mat d)
  unitary_right : val * Matrix.conjTranspose val = (1 : Mat d)

noncomputable def convexUnitaryAction {d : Nat} (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho : Mat d) : Mat d :=
  (lambdas.zipWith
      (fun l u => (Complex.ofReal l) • (u.val * rho * Matrix.conjTranspose u.val))
      unitaries).sum

noncomputable def stochasticAction {d : Nat} (q : Real) (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho_f : DensityMatrix d) (rho : DensityMatrix d) : Mat d :=
  (Complex.ofReal q) • convexUnitaryAction lambdas unitaries rho.val +
    (Complex.ofReal (1 - q)) • rho_f.val

noncomputable def stochastically_simulatable {d : Nat} (E : Channel d) : Prop :=
  Exists fun q : Real =>
  Exists fun lambdas : List Real =>
  Exists fun unitaries : List (UnitaryMat d) =>
  Exists fun rho_f : DensityMatrix d =>
    0 <= q /\ q <= 1 /\
    (List.Forall (fun l => 0 <= l) lambdas) /\
    lambdas.sum = 1 /\
    lambdas.length = unitaries.length /\
    ∀ rho : DensityMatrix d,
      E.map rho.val = stochasticAction q lambdas unitaries rho_f rho

noncomputable def unitarySamples {d : Nat} (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho : DensityMatrix d) : List (Real × Mat d) :=
  lambdas.zipWith (fun l u => (l, u.val * rho.val * Matrix.conjTranspose u.val)) unitaries

noncomputable def expectedSampling {d : Nat} (samples : List (Real × Mat d)) : Mat d :=
  (samples.map (fun s => (Complex.ofReal s.1) • s.2)).sum

noncomputable def stochasticSamples {d : Nat} (q : Real) (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho_f : DensityMatrix d) (rho : DensityMatrix d) :
    List (Real × Mat d) :=
  (unitarySamples lambdas unitaries rho).map (fun s => (q * s.1, s.2)) ++
    [(1 - q, rho_f.val)]

lemma expectedSampling_append {d : Nat} (samples1 samples2 : List (Real × Mat d)) :
    expectedSampling (samples1 ++ samples2) =
      expectedSampling samples1 + expectedSampling samples2 := by
  simp [expectedSampling, List.map_append, List.sum_append]

lemma expectedSampling_map_mul {d : Nat} (q : Real) (samples : List (Real × Mat d)) :
    expectedSampling (samples.map (fun s => (q * s.1, s.2))) =
      (Complex.ofReal q) • expectedSampling samples := by
  sorry

lemma expected_sampling_eq_convexUnitaryAction {d : Nat} (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho : DensityMatrix d) :
    expectedSampling (unitarySamples lambdas unitaries rho) =
      convexUnitaryAction lambdas unitaries rho.val := by
  classical
  induction lambdas generalizing unitaries with
  | nil =>
      cases unitaries <;> simp [unitarySamples, expectedSampling, convexUnitaryAction]
  | cons l ls ih =>
      cases unitaries with
      | nil =>
          simp [unitarySamples, expectedSampling, convexUnitaryAction]
      | cons u us =>
          simp [unitarySamples, expectedSampling, convexUnitaryAction, ih]

lemma expected_sampling_eq_stochasticAction {d : Nat} (q : Real) (lambdas : List Real)
    (unitaries : List (UnitaryMat d)) (rho_f : DensityMatrix d) (rho : DensityMatrix d) :
    expectedSampling (stochasticSamples q lambdas unitaries rho_f rho) =
      stochasticAction q lambdas unitaries rho_f rho := by
  sorry

theorem expected_sampling_eq_channel {d : Nat} {E : Channel d}
    (hE : stochastically_simulatable E) :
    ∃ q lambdas unitaries rho_f,
      0 <= q /\ q <= 1 /\
      (List.Forall (fun l => 0 <= l) lambdas) /\
      lambdas.sum = 1 /\
      lambdas.length = unitaries.length /\
      ∀ rho : DensityMatrix d,
        E.map rho.val =
          expectedSampling (stochasticSamples q lambdas unitaries rho_f rho) := by
  rcases hE with ⟨q, lambdas, unitaries, rho_f, hq0, hq1, hl, hsum, hlen, hmap⟩
  refine ⟨q, lambdas, unitaries, rho_f, hq0, hq1, hl, hsum, hlen, ?_⟩
  intro rho
  calc
    E.map rho.val = stochasticAction q lambdas unitaries rho_f rho := hmap rho
    _ = expectedSampling (stochasticSamples q lambdas unitaries rho_f rho) := by
          symm
          simpa using
            (expected_sampling_eq_stochasticAction (q := q) (lambdas := lambdas)
              (unitaries := unitaries) (rho_f := rho_f) (rho := rho))

end LearningLean.Quantum
