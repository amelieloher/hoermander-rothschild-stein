-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformCentreTimeOneJets
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Positive joint endpoint jets bound displacement linearly in the
coefficient input, uniformly in the initial point. -/
theorem norm_endpoint_sub_initial_of_joint_first_jet_bound {m N : ℕ}
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) {σ C : ℝ} (hσ : 0 < σ)
    (H : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (ball 0 σ ×ˢ Ω))
    (hzero : ∀ x ∈ Ω, H (0,x) = x)
    (hjet : ∀ q ∈ ball 0 σ ×ˢ Ω, ‖iteratedFDeriv ℝ 1 H q‖ ≤ C)
    {c : Fin m → ℝ} (hc : c ∈ ball 0 σ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖H (c,x)-x‖ ≤ C*‖c‖ := by
  let L := ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin N → ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simp [L]
  have hd (y : Fin m → ℝ) (hy : y ∈ ball 0 σ) :
      HasFDerivAt (fun z => H (z,x)) ((fderiv ℝ H (y,x)).comp L) y := by
    have hi : HasFDerivAt (fun z : Fin m → ℝ => (z,x)) L y := by
      simpa [L] using (L.hasFDerivAt (x := y)).const_add ((0 : Fin m → ℝ),x)
    have hh : DifferentiableAt ℝ H (y,x) := (hH.contDiffAt ((isOpen_ball.prod hΩ).mem_nhds ⟨hy,hx⟩)).differentiableAt
      (by simp)
    simpa only [Function.comp_def] using hh.hasFDerivAt.comp y hi
  have hb (y : Fin m → ℝ) (hy : y ∈ ball 0 σ) :
      ‖fderiv ℝ (fun z => H (z,x)) y‖ ≤ C := by
    rw [(hd y hy).fderiv]
    have hh : ‖fderiv ℝ H (y,x)‖ ≤ C := by
      simpa only [norm_iteratedFDeriv_one] using hjet (y,x) ⟨hy,hx⟩
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hL (norm_nonneg _)).trans (by simpa using hh))
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hd y hy).differentiableAt) hb (convex_ball (0 : Fin m → ℝ) σ)
    (by simpa using hσ : (0 : Fin m → ℝ) ∈ ball 0 σ) hc
  simpa only [hzero x hx, sub_zero] using he
end RothschildStein.G3
