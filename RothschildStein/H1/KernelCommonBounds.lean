-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelData
public import RothschildStein.H1.FiniteHomogeneousBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

private def boundWord : Option (Fin (q + 1) × Fin (q + 1)) → List (Fin (q + 1))
  | none => []
  | some p => if p.1 = 0 then [p.2] else [p.1, p.2]

/-- One positive constant simultaneously bounds
Gamma, every horizontal first derivative, and the sum of a horizontal
second derivative and the drift derivative (BB printed p. 538). -/
theorem FundamentalKernel.common_bounds (K : FundamentalKernel G H) :
    ∃ C > 0, ∀ x, x ≠ 0 →
      |K x| ≤ C * (H.norm x) ^ (2 - (G.homogeneousDimension : ℝ)) ∧
      (∀ i : Fin q, |fieldDerivative (H.fields i.succ) K x| ≤
        C * (H.norm x) ^ (1 - (G.homogeneousDimension : ℝ))) ∧
      (∀ i j : Fin q,
        |fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) x| +
          |fieldDerivative (H.fields 0) K x| ≤ C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ))) := by
  let f := fun I : Option (Fin (q + 1) × Fin (q + 1)) => wordDerivative H.fields (boundWord I) K
  let a := fun I : Option (Fin (q + 1) × Fin (q + 1)) =>
    2 - (G.homogeneousDimension : ℝ) - (differentialWordWeight (boundWord I) : ℝ)
  obtain ⟨C, hC, hb⟩ := finite_homogeneous_family_bound G H.norm f a
    (fun I => (H.wordDerivative_smooth_off_zero G K.smooth_off_zero (boundWord I)).continuousOn)
    (fun I => H.wordDerivative_homogeneous G K.smooth_off_zero K.homogeneous (boundWord I))
  refine ⟨2 * C, by positivity, fun x hx => ?_⟩
  have hbase : |K x| ≤ C * (H.norm x) ^ (2 - (G.homogeneousDimension : ℝ)) := by
    simpa only [f, a, boundWord, differentialWordWeight, List.map_nil, List.sum_nil,
      Nat.cast_zero, sub_zero, wordDerivative] using hb none x hx
  have hfirst (i : Fin q) : |fieldDerivative (H.fields i.succ) K x| ≤
      C * (H.norm x) ^ (1 - (G.homogeneousDimension : ℝ)) := by
    have hi := hb (some (0, i.succ)) x hx
    have ha : a (some (0, i.succ)) = 1 - (G.homogeneousDimension : ℝ) := by
      simp only [a, boundWord, ite_true, differentialWordWeight, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Fin.succ_ne_zero, ite_false]
      norm_num
      ring
    rw [ha] at hi
    exact hi
  have hdrift : |fieldDerivative (H.fields 0) K x| ≤
      C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ)) := by
    have hi := hb (some (0, 0)) x hx
    have ha : a (some (0, 0)) = -(G.homogeneousDimension : ℝ) := by
      simp only [a, boundWord, ite_true, differentialWordWeight, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      norm_num
    rw [ha] at hi
    exact hi
  have hsecond (i j : Fin q) :
      |fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) x| ≤
      C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ)) := by
    have hi := hb (some (i.succ, j.succ)) x hx
    have ha : a (some (i.succ, j.succ)) = -(G.homogeneousDimension : ℝ) := by
      simp only [a, boundWord, Fin.succ_ne_zero, ite_false, differentialWordWeight,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num
    rw [ha] at hi
    exact hi
  have hcoeff : C ≤ 2 * C := by linarith
  refine ⟨hbase.trans (mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (H.norm.gauge.2.1 x) _)), fun i =>
    (hfirst i).trans (mul_le_mul_of_nonneg_right hcoeff
      (Real.rpow_nonneg (H.norm.gauge.2.1 x) _)), fun i j => ?_⟩
  calc
    _ ≤ C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ)) +
        C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ)) := add_le_add (hsecond i j) hdrift
    _ = _ := by ring

end RothschildStein.H1
