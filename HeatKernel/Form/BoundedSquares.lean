-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ContinuouslyDifferentiableComposition
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Squares of bounded energy-domain functions

A compactly supported scalar modification of the square agrees with it on the essential
range of a bounded function. The scalar chain rule therefore gives its horizontal derivative.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace HeatKernel

/-- The square of a bounded energy-domain function belongs to the domain, with derivative
 twice the function times its horizontal derivative. -/
theorem exists_energyGraph_square_of_ae_bound {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X)
    {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ᵐ x ∂volume, ‖(v : GradientSpace (N := N) ⊤ q).fst x‖ ≤ M) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => ((v : GradientSpace (N := N) ⊤ q).fst x) ^ 2) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => 2 * (v : GradientSpace (N := N) ⊤ q).fst x *
          (v : GradientSpace (N := N) ⊤ q).snd i x) := by
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := M + 1
      rOut := M + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := fun s => s ^ 2 * φ s
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := (contDiff_id.pow 2).mul φ.contDiff
  have hcompact : HasCompactSupport η := φ.hasCompactSupport.mul_left
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous (hη.continuous_deriv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hzero : η 0 = 0 := by simp only [η, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have hagree : ∀ s, ‖s‖ ≤ M → η s = s ^ 2 ∧ deriv η s = 2 * s := by
    intro s hs
    have hball : s ∈ Metric.ball (0 : ℝ) φ.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hs (by dsimp [φ]; linarith)
    have he : η =ᶠ[𝓝 s] fun t => t ^ 2 :=
      (φ.eventuallyEq_one_of_mem_ball hball).mono fun t ht => by simp only [η, ht, Pi.one_apply, mul_one]
    have hd : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 s
    exact ⟨he.self_of_nhds, (hd.congr_of_eventuallyEq he).deriv⟩
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_comp_contDiff_one X hX v
    (hη.of_le (by simp)) hzero (C := ⟨C, hC0⟩) hC
  refine ⟨z, ?_, fun i => ?_⟩
  · filter_upwards [hzf, hv] with x hx hbound
    exact hx.trans ((hagree _ hbound).1)
  · filter_upwards [hzg i, hv] with x hx hbound
    rw [(hagree _ hbound).2] at hx
    exact hx

end HeatKernel
