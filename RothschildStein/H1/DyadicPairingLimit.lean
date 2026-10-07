-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicLimitProperties
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The uniform dyadic limit may be paired with every compact
continuous function, using local integrability and dominated convergence
(BB p. 266). -/
theorem tendsto_integral_scaledFundamentalKernel
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ ω : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω)
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x)
    {ψ : (Fin N → ℝ) → ℝ} (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Tendsto (fun n : ℕ => ∫ x, scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x * ψ x)
      atTop (𝓝 (∫ x, fundamentalDyadicLimit G Γ ω x * ψ x)) := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  let F := fundamentalDyadicLimit G Γ ω
  have hF : LocallyIntegrable F := locallyIntegrable_fundamentalDyadicLimit G hQ hΓ hsm hs
  have hi : Integrable (fun x => F x * ψ x) :=
    hF.integrable_smul_right_of_hasCompactSupport hψ hcompact
  have hiψ : Integrable ψ := hψ.integrable_of_hasCompactSupport hcompact
  have hu := tendstoUniformlyOn_scaledFundamentalKernel G hQ hsm hs hω
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖F x * ψ x‖ + ‖ψ x‖)
  · apply Eventually.of_forall
    intro n
    have hn : LocallyIntegrable (scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ) :=
      locallyIntegrable_scaledFundamentalKernel G hΓ (pow_pos (by norm_num : (0 : ℝ) < 2) n)
    exact (hn.integrable_smul_right_of_hasCompactSupport hψ hcompact).aestronglyMeasurable
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with n hn
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    have hd : ‖scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x - F x‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn x hx
    have hb : ‖scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x‖ ≤ ‖F x‖ + 1 := by
      have ht := norm_add_le (scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x - F x) (F x)
      have he : scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x - F x + F x =
        scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x := by ring
      rw [he] at ht
      linarith
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (ψ x)]
  · exact hi.norm.add hiψ.norm
  · filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    exact (hu.tendsto_at hx).mul_const (ψ x)

end RothschildStein.H1
