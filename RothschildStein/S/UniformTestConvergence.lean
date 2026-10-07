-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.LocalConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal Distributions
namespace RothschildStein.S
variable {n : ℕ}

/-- Uniform convergence on the compact support of a test gives
convergence of regular-distribution evaluations (BB pp. 68–69). -/
theorem tendsto_testIntegral_of_uniformOnSupport {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated]
    (Ω : Opens (Fin n → ℝ)) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (F : α → (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hF : ∀ j, LocallyIntegrableOn (F j) (Ω : Set (Fin n → ℝ)) volume)
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume)
    (ht : TendstoUniformlyOn F f l (tsupport φ)) :
    Tendsto (fun j => Distribution.ofFun Ω (F j) volume (⊤ : ℕ∞) φ) l
      (𝓝 (Distribution.ofFun Ω f volume (⊤ : ℕ∞) φ)) := by
  have hi : Integrable (fun x => φ x * f x) volume := by
    simpa only [smul_eq_mul] using φ.integrable_smul hf
  have hb : Integrable (fun x => ‖φ x * f x‖ + ‖φ x‖) volume :=
    hi.norm.add (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hu := (Metric.tendstoUniformlyOn_iff.mp ht) 1 zero_lt_one
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (f := fun x => φ x • f x) (fun x => ‖φ x * f x‖ + ‖φ x‖)
    (Eventually.of_forall (fun j => (φ.integrable_smul (hF j)).aestronglyMeasurable))
    (hu.mono fun j hj => Eventually.of_forall fun x => ?_)
    hb (Eventually.of_forall fun x => ?_)
  · rw [Distribution.ofFun_apply hf]
    exact hh.congr (fun j => (Distribution.ofFun_apply (hF j)).symm)
  · by_cases hx : x ∈ tsupport φ
    · have hd : ‖F j x - f x‖ ≤ 1 := by
        simpa only [dist_eq_norm, norm_sub_rev] using (hj x hx).le
      have hn : ‖F j x‖ ≤ ‖f x‖+1 := by
        calc
          _ ≤ ‖F j x-f x‖+‖f x‖ := norm_le_norm_sub_add _ _
          _ ≤ _ := by linarith
      simpa only [smul_eq_mul,norm_mul,mul_add,mul_one] using
        (mul_le_mul_of_nonneg_left hn (norm_nonneg (φ x)))
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · by_cases hx : x ∈ tsupport φ
    · exact tendsto_const_nhds.smul (ht.tendsto_at hx)
    · simpa [image_eq_zero_of_notMem_tsupport hx] using
        (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))

end RothschildStein.S
