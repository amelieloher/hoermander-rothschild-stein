-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceFirstVariation
public import RothschildStein.G1.SmoothDependenceLinearFamily

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Identify the initial-data derivative for both signs of
time using an independent fundamental solution on a common symmetric
interval (BB Proposition 1.2, p. 3). -/
theorem flow_hasFDerivAt_initial_of_fundamental_solution_signed
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {Φ : E → ℝ → E} {x : E} {S B : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hc : ∀ᶠ y in 𝓝 x, ContinuousOn (Φ y) (Icc (-S) S))
    (hsol : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (-S) S, HasDerivAt (Φ y) (Z (Φ y t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, Φ y 0 = y)
    (hmem : ∀ t ∈ Icc (-S) S, Φ x t ∈ Ω)
    (hLip : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (-S) S, ‖Φ y t - Φ x t‖ ≤ B * ‖y - x‖)
    {J : ℝ → E →L[ℝ] E} (hJ : ContinuousOn J (Icc (-S) S))
    (hJ' : ∀ t ∈ Icc (-S) S,
      HasDerivAt J ((fderiv ℝ Z (Φ x t)).comp (J t)) t)
    (hJinit : J 0 = ContinuousLinearMap.id ℝ E) :
    ∀ t ∈ Icc (-S) S, HasFDerivAt (fun y => Φ y t) (J t) x := by
  intro t ht
  rcases le_total 0 t with hpos | hneg
  · have hs : Icc 0 t ⊆ Icc (-S) S := Icc_subset_Icc (by linarith) ht.2
    apply flow_hasFDerivAt_initial_of_fundamental_solution hΩ hZ hB
      (hc.mono (fun _ hy => hy.mono hs))
      (hsol.mono (fun _ hy v hv => hy v (hs (Ico_subset_Icc_self hv))))
      hinit (fun v hv => hmem v (hs hv))
      (hLip.mono (fun _ hy v hv => hy v (hs hv))) (hJ.mono hs)
      (fun v hv => hJ' v (hs (Ico_subset_Icc_self hv))) hJinit t ⟨hpos, le_rfl⟩
  · have hs : MapsTo (fun v : ℝ => -v) (Icc 0 (-t)) (Icc (-S) S) := by
      intro v hv
      constructor <;> linarith [hv.1, hv.2, ht.1]
    have hc' : ∀ᶠ y in 𝓝 x, ContinuousOn (fun v => Φ y (-v)) (Icc 0 (-t)) :=
      hc.mono (fun _ hy => hy.comp continuous_neg.continuousOn hs)
    have hd' : ∀ᶠ y in 𝓝 x, ∀ v ∈ Ico 0 (-t),
        HasDerivAt (fun s => Φ y (-s)) (-Z (Φ y (-v))) v := by
      filter_upwards [hsol] with y hy
      intro v hv
      simpa only [Function.comp_def, neg_one_smul] using
        (hy (-v) (hs (Ico_subset_Icc_self hv))).scomp v (hasDerivAt_neg v)
    have hJd' : ∀ v ∈ Ico 0 (-t),
        HasDerivAt (fun s => J (-s))
          ((fderiv ℝ (fun z => -Z z) (Φ x (-v))).comp (J (-v))) v := by
      intro v hv
      simpa only [Function.comp_def, neg_one_smul, fderiv_fun_neg,
        ContinuousLinearMap.neg_comp] using
        (hJ' (-v) (hs (Ico_subset_Icc_self hv))).scomp v (hasDerivAt_neg v)
    have hi' : ∀ᶠ y in 𝓝 x, Φ y (-0) = y := by simpa only [neg_zero] using hinit
    have hb := flow_hasFDerivAt_initial_of_fundamental_solution hΩ hZ.neg hB
      hc' hd' hi' (fun v hv => hmem (-v) (hs hv))
      (hLip.mono (fun _ hy v hv => hy (-v) (hs hv)))
      (hJ.comp continuous_neg.continuousOn hs) hJd'
      (by simpa only [Function.comp_def, neg_zero] using hJinit) (-t) ⟨by linarith, le_rfl⟩
    simpa only [Function.comp_def, neg_neg] using hb

end RothschildStein.G1
