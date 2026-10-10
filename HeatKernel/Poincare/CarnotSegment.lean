-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MetricSegment
public import HeatKernel.Geometry.CarnotPoint
public import HeatKernel.Geometry.HorizontalSubarc

/-! Constant-speed minimizing metric segments in homogeneous horizontal geometry. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel.CarnotPoint

/-- A homogeneous horizontal metric with bracket-spanning weight-one generators has
minimizing constant-speed metric segments. No minimizing horizontal controls are required. -/
theorem exists_metric_segment {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x y : CarnotPoint G hq hqpos hspan) :
    ∃ γ : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (γ s) (γ t) = dist x y * dist s t := by
  let := properSpace G hq hqpos hspan hw
  apply exists_metric_segment_of_approximate_paths x y
  intro ε hε
  by_cases hxy : x = y
  · subst y
    exact ⟨fun _ => x, rfl, rfl, fun s t => by simp; positivity⟩
  have hD : 0 < dist x y := dist_pos.mpr hxy
  have hd0 : 0 < horizontalL2Distance (G.horizontalFields hq) x y := by
    change 0 < edist x y
    exact edist_pos.mpr hxy
  have hdf : horizontalL2Distance (G.horizontalFields hq) x y ≠ ⊤ := edist_ne_top x y
  obtain ⟨ℓ, γ, a, hℓ, hlength, hx, hy, hγ, ha, _⟩ :=
    exists_horizontal_nearGeodesic hd0 hdf (div_pos hε hD)
  have hreal : (horizontalL2Distance (G.horizontalFields hq) x y).toReal = dist x y :=
    (dist_edist x y).symm
  rw [hreal] at hlength
  have he : (1 + ε / dist x y) * dist x y = dist x y + ε := by
    field_simp [hD.ne']
  rw [he] at hlength
  let g : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan := fun t => γ (ℓ * (t : ℝ))
  have hordered : ∀ s t : Icc (0 : ℝ) 1, (s : ℝ) ≤ t →
      dist (g s) (g t) ≤ (dist x y + ε) * dist s t := by
    intro s t hst
    have hsub := hγ.subarc_distance_le_of_controlNorm_le_one
      (show 0 ≤ ℓ * (s : ℝ) from mul_nonneg hℓ.le s.2.1)
      (show ℓ * (s : ℝ) ≤ ℓ * (t : ℝ) from mul_le_mul_of_nonneg_left hst hℓ.le)
      (show ℓ * (t : ℝ) ≤ ℓ by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2 hℓ.le) (fun u _ => ha u)
    have hdiff : 0 ≤ ℓ * (t : ℝ) - ℓ * (s : ℝ) :=
      sub_nonneg.mpr (mul_le_mul_of_nonneg_left hst hℓ.le)
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsub
    rw [ENNReal.toReal_ofReal hdiff] at hb
    have hd : dist (g s) (g t) ≤ ℓ * ((t : ℝ) - s) := by
      rw [dist_edist, edist_eq]
      dsimp only [g]
      convert hb using 1
      ring
    have hparam : dist s t = (t : ℝ) - s := by
      change |(s : ℝ) - t| = (t : ℝ) - s
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    rw [hparam]
    exact hd.trans (mul_le_mul_of_nonneg_right hlength.le (sub_nonneg.mpr hst))
  refine ⟨g, ?_, ?_, ?_⟩
  · change γ (ℓ * (0 : ℝ)) = x
    simpa only [mul_zero] using hx
  · change γ (ℓ * (1 : ℝ)) = y
    simpa only [mul_one] using hy
  · intro s t
    rcases le_total (s : ℝ) t with hst | hts
    · exact hordered s t hst
    · simpa only [dist_comm] using hordered t s hts

end HeatKernel.CarnotPoint
