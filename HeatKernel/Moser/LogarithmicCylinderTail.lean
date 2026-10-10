-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicRelativeTail
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Relative logarithmic tails on product cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A compact-interval tail cost controlled by the reference cylinder mass
gives the relative tail estimate on the corresponding open interval. -/
theorem logarithmic_cylinder_tail_of_energy_cost
    {E : Type*} [MeasurableSpace E] (spatial : Measure E) [SFinite spatial]
    {V : Set E} (hV : MeasurableSet V) (hVfinite : spatial V ≠ ⊤)
    {p q c d ℓ K D A : ℝ} (hpq : p ≤ q) (hcd : c ≤ d) (hℓ : 0 < ℓ)
    {T : Set (ℝ × E)}
    (hcost : max (324 * K) (2 * D * (q - p) * ((q - p) * spatial.real V)) ≤
      A * ((d - c) * spatial.real V))
    (htail : ((volume.restrict (Ioc p q)).prod (spatial.restrict V)).real T ≤
      max (324 * K) (2 * D * (q - p) *
        ((volume.restrict (Ioc p q)).prod (spatial.restrict V)).real univ) / ℓ) :
    (volume.prod spatial) ((Ioo p q ×ˢ V) ∩ T) ≤
      ENNReal.ofReal (A / ℓ) * (volume.prod spatial) (Ioo c d ×ˢ V) := by
  have hWfinite : (volume.prod spatial) (Ioc p q ×ˢ V) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfinite
  have hRfinite : (volume.prod spatial) (Ioo c d ×ˢ V) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfinite
  have hmass : ((volume.restrict (Ioc p q)).prod (spatial.restrict V)).real univ =
      (q - p) * spatial.real V := by
    rw [show (univ : Set (ℝ × E)) = univ ×ˢ univ by simp, measureReal_prod_prod]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]
  apply logarithmic_relative_tail_of_real_cost
    (B := max (324 * K) (2 * D * (q - p) *
      ((volume.restrict (Ioc p q)).prod (spatial.restrict V)).real univ))
    (measurableSet_Ioc.prod hV) hWfinite hRfinite
    (fun z hz => ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩) hℓ
  · rw [← Measure.prod_restrict]
    exact htail
  · rw [hmass, measureReal_prod_prod, Real.volume_real_Ioo_of_le hcd]
    exact hcost

end HeatKernel
