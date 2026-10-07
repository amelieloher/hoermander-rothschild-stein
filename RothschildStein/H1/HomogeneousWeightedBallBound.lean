-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousKernelIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Steps 2 and 4: homogeneous kernels above degree −Q
have a uniform Cρ^(Q+β) small-ball bound against any test weight with
a fixed pointwise bound. -/
theorem exists_homogeneousKernel_weightedBall_bound
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) {β B : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : -(G.homogeneousDimension : ℝ) < β) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ g : (Fin N → ℝ) → ℝ,
      (∀ w, ‖g w‖ ≤ B) → ‖∫ w in {w | ν w ≤ ρ}, f w * g w‖ ≤
        C * ρ ^ ((G.homogeneousDimension : ℝ) + β) := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  obtain ⟨Cf, hCf, hb⟩ := exists_homogeneousKernel_gauge_bound G hν hf hhom
  have hd : 0 < (G.homogeneousDimension : ℝ) + β := by linarith
  let C := (Cf * B) * ((G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal) /
    ((G.homogeneousDimension : ℝ) + β)
  refine ⟨C, div_nonneg (mul_nonneg (mul_nonneg hCf hB)
    (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)) hd.le, ?_⟩
  intro ρ hρ g hg
  have hp : IntegrableOn (fun w => (ν w) ^ β) {w | ν w ≤ ρ} volume := by
    simpa only [neg_neg] using (G2.integrableOn_power_near_iff hν (-β) hρ).mpr (by linarith)
  have heq : (∫ w in {w | ν w ≤ ρ}, (ν w) ^ β) =
      (G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal *
        ρ ^ ((G.homogeneousDimension : ℝ) + β) / ((G.homogeneousDimension : ℝ) + β) := by
    simpa only [neg_neg, sub_neg_eq_add] using G2.integral_power_near hν (β := -β) (by linarith) hρ
  calc
    _ ≤ ∫ w in {w | ν w ≤ ρ}, (Cf * B) * (ν w) ^ β := by
      apply norm_integral_le_of_norm_le (hp.const_mul (Cf * B))
      filter_upwards [(volume.ae_ne (0 : Fin N → ℝ)).filter_mono ae_restrict_le] with w hw
      rw [norm_mul]
      calc
        _ ≤ (Cf * (ν w) ^ β) * B := mul_le_mul (hb w hw) (hg w) (norm_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg (hν.2.1 w) _))
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul, heq]; dsimp [C]; ring

end RothschildStein.H1
