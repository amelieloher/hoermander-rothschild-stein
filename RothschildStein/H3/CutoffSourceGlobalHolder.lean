-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothSourceFrozenHolder
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- An arbitrary interior smooth test localizes actual Holder
forcing to a finite global Holder source, without a gauge-ball premise
on its original domain. -/
theorem cutoff_source_global_holder_finite_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (V : Opens (Fin N → ℝ)) {a : ℝ≥0} (ha1 : a ≤ 1)
    (f : (Fin N → ℝ) → ℝ)
    (hf : holderENorm (controlDistance univ driftWeight H.fields) a (V : Set (Fin N → ℝ)) f < ⊤)
    (χ : TestFunction V ℝ (⊤ : ℕ∞)) :
    holderENorm (controlDistance univ driftWeight H.fields) a univ (fun x => χ x * f x) < ⊤ := by
  let metric := gaugeMetric G C.norm C.constant_one C.symmetric
  obtain ⟨R, hR⟩ := χ.hasCompactSupport.bddAbove_image C.norm.gauge.1.continuousOn
  have hs : tsupport (χ : (Fin N → ℝ) → ℝ) ⊆ {x | C.norm x < R + 1} := by
    intro x hx
    change C.norm.toFun x < R + 1
    exact (hR ⟨x, hx, rfl⟩).trans_lt (by linarith)
  have hχ := smooth_source_global_holder_finite_of_controlNorm G H.fields C a ha1 (R + 1)
    χ χ.contDiff χ.hasCompactSupport hs
  rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hχ hf ⊢
  exact (boundedHolderNorm_cutoff_product_of_controlNorm C V.isOpen χ.hasCompactSupport χ.tsupport_subset
    hχ hf).trans_lt (ENNReal.mul_lt_top hχ hf)

end RothschildStein.H3
