-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.WeakHorizontalGradient
public import HeatKernel.Moser.LocalHorizontalDerivatives

/-! Local horizontal Sobolev membership of horizontal metric Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- Continuous functions with locally bounded weak horizontal gradients are locally
first-order horizontal Sobolev functions. -/
theorem memSobolevXLoc_of_bounded_weak_gradient {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    (g : Fin q → (Fin N → ℝ) → ℝ)
    (hg : ∀ i, hasWeakWordDeriv X ⊤ [i] f (g i)) {C : ℝ}
    (hb : ∀ i, ∀ᵐ x ∂volume, |g i x| ≤ C) : memSobolevXLoc noDriftWeight X ⊤ 1 2 f := by
  intro V hV _hsub
  let μ := volume.restrict (V : Set (Fin N → ℝ))
  have hm : volume (V : Set (Fin N → ℝ)) < ⊤ :=
    (measure_mono subset_closure).trans_lt hV.measure_lt_top
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hm.ne
  apply memSobolevX_noDrift_one_two_iff.mpr
  constructor
  · obtain ⟨B, hB⟩ := hV.exists_bound_of_continuousOn hf.continuousOn
    apply (memLp_const B).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact hB x (subset_closure hx)
  · intro i
    refine ⟨g i, S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) (hg i), ?_⟩
    have hmeas : AEStronglyMeasurable (g i) volume :=
      (locallyIntegrableOn_univ.mp (by simpa only [Opens.coe_top] using (hg i).2.1)).aestronglyMeasurable
    apply (memLp_const C).mono' hmeas.restrict
    filter_upwards [ae_restrict_of_ae (hb i)] with x hx
    simpa only [Real.norm_eq_abs] using hx

/-- Horizontal Lipschitz functions belong to the literal local first-order Sobolev class. -/
theorem memSobolevXLoc_of_horizontalLipschitz {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (L : ℝ≥0) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y) :
    memSobolevXLoc noDriftWeight (G.horizontalFields hq) ⊤ 1 2 f := by
  obtain ⟨g, hg, hb⟩ := exists_weak_horizontal_gradient G hq L hf hLip
  apply memSobolevXLoc_of_bounded_weak_gradient (G.horizontalFields hq) hf g hg
  intro i
  filter_upwards [hb] with x hx
  exact (abs_control_le_controlNorm (fun i _ => g i x) i 0).trans hx

/-- Lipschitz functions on the horizontal metric carrier are locally horizontal Sobolev. -/
theorem CarnotPoint.memSobolevXLoc_of_lipschitz {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    memSobolevXLoc noDriftWeight (G.horizontalFields hq) ⊤ 1 2 f :=
  memSobolevXLoc_of_horizontalLipschitz G hq L hf.continuous (fun x y => hf x y)

end HeatKernel
