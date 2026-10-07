-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RothschildStein.Geometry

/-- A continuous right-hand side upgrades an absolutely continuous scalar
trajectory's almost-everywhere ODE to a derivative on the closed interval. -/
theorem scalar_trajectory_hasDerivWithinAt {γ f : ℝ → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hf : ContinuousOn f (Icc 0 1))
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 1), HasDerivAt γ (f t) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (f t) (Icc 0 1) t := by
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (fun t : Icc (0 : ℝ) 1 => f t)
  have hg : Continuous g := (hf.domRestrict).Icc_extend'
  have he : ∀ t ∈ Icc (0 : ℝ) 1, g t = f t := by
    intro t ht
    simp [g, IccExtend, projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) ht]
  let G := fun t => ∫ v in (0 : ℝ)..t, g v
  have hG : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hGac : AbsolutelyContinuousOnInterval G 0 1 :=
    (hg.intervalIntegrable 0 1).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hd' : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt γ (f t) t :=
    (ae_restrict_iff' measurableSet_Icc).mp hd
  obtain ⟨c, hc⟩ := (hγ.sub hGac).const_of_ae_hasDerivAt_zero (by
    filter_upwards [hd'] with t ht hmem
    have hm : t ∈ Icc (0 : ℝ) 1 := by simpa using hmem
    simpa [he t hm] using (ht hm).sub (hG t))
  have hEq : EqOn γ (fun t => G t + c) (Icc 0 1) := by
    intro t ht
    have hh := hc t (by simpa using ht)
    change γ t - G t = c at hh
    linarith
  intro t ht
  rw [← he t ht]
  exact ((hG t).add_const c).hasDerivWithinAt.congr hEq (hEq ht)

/-- Coordinatewise fundamental theorem of calculus for a continuous vector ODE. -/
theorem trajectory_hasDerivWithinAt {n : ℕ} {γ f : ℝ → (Fin n → ℝ)}
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hf : ContinuousOn f (Icc 0 1))
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 1), HasDerivAt γ (f t) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (f t) (Icc 0 1) t := by
  intro t ht
  apply hasDerivWithinAt_pi.mpr
  intro i
  have hac : AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1 :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).lipschitzWith.comp_absolutelyContinuousOnInterval hγ
  apply scalar_trajectory_hasDerivWithinAt hac ((continuous_apply i).comp_continuousOn hf)
    (Filter.Eventually.mono hd (fun _ h => (hasDerivAt_pi.mp h) i)) t ht

end RothschildStein.Geometry
