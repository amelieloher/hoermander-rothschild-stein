-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotOscillationEnergy
public import HeatKernel.Poincare.MeanShiftExtended

/-! Same-ball mean oscillation estimates from horizontal energy. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Replacing the auxiliary Whitney constant by the ball mean costs exactly the
factor 2^p, without a preliminary oscillation integrability assumption. -/
theorem lintegral_mean_oscillation_le_horizontal_energy {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r κ p : ℝ} (hr : 0 < r) (hκ : 240 < κ)
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r))
    (hf : IntegrableOn u (horizontalBall (G.horizontalFields hq) x r)) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z| ^ p)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p) *
      (ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2)) ^ p) *
        ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension)) *
        ENNReal.ofReal ((2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ)) ^ (p - 1)) *
        ENNReal.ofReal ((κ + 13) ^ G.homogeneousDimension) * ENNReal.ofReal r *
        (1000 ^ G.homogeneousDimension : ℕ) *
        ∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
          ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u y ^ p) := by
  let B := horizontalBall (G.horizontalFields hq) x r
  let _ : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  let _ : NeZero (volume B) := ⟨(volume_horizontalBall_pos G hq hqpos hspan x hr).ne'⟩
  obtain ⟨c, hc⟩ := exists_const_lintegral_oscillation_le_horizontal_energy
    G hq hqpos hspan hw x hr hκ k hk hscale hp u hu
  have hs := lintegral_abs_sub_average_rpow_le_const_of_integrable
    (μ := volume.restrict B) hp hf c
  exact (hs.trans (mul_le_mul_right hc (ENNReal.ofReal ((2 : ℝ) ^ p)))).trans_eq (by ac_rfl)

end HeatKernel
