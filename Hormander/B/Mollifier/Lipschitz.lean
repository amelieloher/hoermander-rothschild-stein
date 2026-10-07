-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section

open scoped SchwartzMap

namespace Hormander.B

variable {N : ℕ}

/-- A Schwartz function with values in a normed space is globally Lipschitz. -/
theorem schwartz_lipschitz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : 𝓢(Carrier N, F)) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Carrier N, ‖φ x - φ y‖ ≤ L * ‖x - y‖ := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ (Carrier N) F φ),
    by positivity, fun x y => ?_⟩
  have hb : ∀ z : Carrier N, ‖fderiv ℝ φ z‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ (Carrier N) F φ) := fun z => by
    have := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.fderivCLM ℝ (Carrier N) F φ) z
    simpa [SchwartzMap.fderivCLM_apply] using this
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ) (s := Set.univ)
    (fun z _ => φ.differentiableAt) (fun z _ => hb z) convex_univ (Set.mem_univ y)
    (Set.mem_univ x)
  simpa [norm_sub_rev] using this

/-- Mixed second differences of a Schwartz function are bounded by the product of increments. -/
theorem schwartz_mixed_difference {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : 𝓢(Carrier N, F)) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x d e : Carrier N,
      ‖φ (x + d + e) - φ (x + d) - φ (x + e) + φ x‖ ≤ L * (‖d‖ * ‖e‖) := by
  obtain ⟨L, hL0, hL⟩ := schwartz_lipschitz (SchwartzMap.fderivCLM ℝ (Carrier N) F φ)
  refine ⟨L, hL0, fun x d e => ?_⟩
  set h : Carrier N → F := fun y => φ (y + e) - φ y with hh
  have hd : ∀ y, HasFDerivAt h (fderiv ℝ φ (y + e) - fderiv ℝ φ y) y := fun y => by
    have h1 : HasFDerivAt (fun y => φ (y + e)) (fderiv ℝ φ (y + e)) y := by
      have h2 : HasFDerivAt (fun y : Carrier N => y + e) (ContinuousLinearMap.id ℝ _) y :=
        (hasFDerivAt_id y).add_const e
      have h3 := HasFDerivAt.comp y (φ.differentiableAt (x := y + e)).hasFDerivAt h2
      rw [ContinuousLinearMap.comp_id] at h3
      exact h3
    exact h1.sub (φ.differentiableAt.hasFDerivAt)
  have hb : ∀ y, ‖fderiv ℝ φ (y + e) - fderiv ℝ φ y‖ ≤ L * ‖e‖ := fun y => by
    have := hL (y + e) y
    simpa [SchwartzMap.fderivCLM_apply] using this
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := h) (s := Set.univ)
    (fun z _ => (hd z).differentiableAt) (fun z _ => by rw [(hd z).fderiv]; exact hb z)
    convex_univ (Set.mem_univ x) (Set.mem_univ (x + d))
  have e1 : h (x + d) - h x = φ (x + d + e) - φ (x + d) - φ (x + e) + φ x := by
    simp only [hh]; abel
  rw [e1] at this
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

end Hormander.B
