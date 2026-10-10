-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AnnularCutoff
public import HeatKernel.Geometry.CompactLipschitzEnergy
public import HeatKernel.Form.LevelSetGradient
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Sharp square-integrable gradients of the logarithmic distance tent -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- The literal distance tent has a closed-energy representative with squared
horizontal gradient bounded by the inverse squared radius and vanishing almost
everywhere outside the open supporting ball, including its boundary. -/
theorem exists_logarithmic_tent_energy_gradient {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    ∃ e : energyGraph (N := N) ⊤ (G.horizontalFields hq),
      (e : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) ∧
      (∀ᵐ y ∂volume, ∑ i, ((e : GradientSpace (N := N) ⊤ q).snd i y) ^ 2 ≤ (r ^ 2)⁻¹) ∧
      ∀ᵐ y ∂volume, y ∉ horizontalBall (G.horizontalFields hq) x r →
        ∀ i, (e : GradientSpace (N := N) ⊤ q).snd i y = 0 := by
  let η : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0
  have heq : annularCutoff x 0 (2 * r) = η := by
    funext y
    have ha : ((0 + 2 * r) / 2 - dist x y) * (2 / (2 * r - 0)) =
        1 - dist x y / r := by field_simp; ring
    have hb : max (1 - dist x y / r) 0 ≤ 1 :=
      max_le (by have := div_nonneg (dist_nonneg : 0 ≤ dist x y) hr.le; linarith) (by norm_num)
    dsimp only [annularCutoff, η]
    rw [ha, max_comm (0 : ℝ)]
    exact min_eq_right hb
  obtain ⟨hl, hc, _, _, _⟩ := CarnotPoint.annularCutoff_spec G hq hqpos hspan hw x
    (r := 0) (R := 2 * r) (by positivity)
  rw [heq] at hl hc
  have hconstant : 2 / (2 * r - 0) = r⁻¹ := by field_simp; ring
  rw [hconstant] at hl
  obtain ⟨e, hv, hb⟩ := CarnotPoint.exists_energyGraph_of_compact_lipschitz G hq hqpos hspan hl hc
  have hη (y : CarnotPoint G hq hqpos hspan) :
      η y = max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 := by
    dsimp only [η]
    rw [dist_edist, CarnotPoint.edist_eq]
  have hv' : (e : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) := by
    filter_upwards [hv] with y hy
    have hh : (e : GradientSpace (N := N) ⊤ q).fst y = η y := by
      simpa only [energyInclusion_apply] using hy
    exact hh.trans (hη y)
  refine ⟨e, hv', ?_, ?_⟩
  · filter_upwards [hb] with y hy
    simp only [Real.coe_toNNReal _ (inv_nonneg.mpr hr.le), energyGradient_apply] at hy
    rw [← inv_pow]
    have hs : 0 ≤ ∑ i, ((e : GradientSpace (N := N) ⊤ q).snd i y) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, ((e : GradientSpace (N := N) ⊤ q).snd i y) ^ 2),
      inv_nonneg.mpr hr.le]
  · have hz := ae_all_iff.mpr (fun i => energyGraph_gradient_zero_on_level
      (G.horizontalFields hq) (G.horizontalFields_contDiff hq) e 0 i)
    filter_upwards [hv', hz] with y hv hz hy i
    apply hz i
    rw [hv, ← hη (y : CarnotPoint G hq hqpos hspan)]
    dsimp only [η]
    have hn : r ≤ dist x (y : CarnotPoint G hq hqpos hspan) := by
      apply le_of_not_gt
      intro hlt
      apply hy
      change edist x (y : CarnotPoint G hq hqpos hspan) < ENNReal.ofReal r
      exact edist_lt_ofReal.mpr hlt
    have hd : 1 ≤ dist x (y : CarnotPoint G hq hqpos hspan) / r :=
      (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hn)
    exact max_eq_right (by linarith)

end HeatKernel
