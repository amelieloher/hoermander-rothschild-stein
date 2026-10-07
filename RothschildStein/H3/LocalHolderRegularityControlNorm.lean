-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalHolderRepresentative
public import RothschildStein.H3.InteriorHolderEstimate
public import RothschildStein.H3.LocalHolderContinuity
public import RothschildStein.S.ContinuousSupNorm
public import RothschildStein.Provider.GroupRegularityInputs
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The two conclusions hold for the standing drift frame and its
distribution equation under the global control-norm hypotheses. -/
theorem localHolderRegularity_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ : G2.GroupMollifier G C.norm)
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.LocalHolderRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  constructor
  · intro α hα hα1 Ω T f hf heq
    let a := Real.toNNReal α
    have hae : (a : ℝ) = α := Real.coe_toNNReal _ hα.le
    have ha : 0 < a := Real.toNNReal_pos.mpr hα
    have ha1 : (a : ℝ) < 1 := by rw [hae]; exact hα1
    have hf' : memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 0 a f := by
      simpa only [hae] using hf
    have hb := global_holder_representative_of_controlNorm G H K hQ C φ Ω ha ha1 T f hf' heq
    simpa only [hae] using hb
  · intro α hα hα1 Ω A V hAK hAV hVK hVΩ
    let a := Real.toNNReal α
    have hae : (a : ℝ) = α := Real.coe_toNNReal _ hα.le
    have ha : 0 < a := Real.toNNReal_pos.mpr hα
    have ha1 : (a : ℝ) < 1 := by rw [hae]; exact hα1
    obtain ⟨B, hB, hest⟩ := interior_holder_estimate_of_controlNorm G H K hQ C μ φ
      (G2.smoothNorm G) (G2.smoothNorm_smooth G) V A hAK hAV ha ha1
    refine ⟨B, hB, ?_⟩
    intro u f hu heq hf
    have hu' : memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 2 a u := by
      simpa only [hae] using hu
    have hv : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) V 2 a u :=
      hu' V hVK hVΩ
    have hf' : holderENorm (controlDistance univ driftWeight H.fields) a (V : Set (Fin N → ℝ)) f < ⊤ := by
      simpa only [hae] using hf
    have huc := continuousOn_of_memHolderXLoc_of_controlNorm G H C Ω 2 ha hu'
    have hV : V ≤ Ω := subset_closure.trans hVΩ
    have hev := frozen_drift_equation_restrict Ω V hV H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) u f
      (huc.locallyIntegrableOn Ω.isOpen.measurableSet) heq
    have hb := hest u f hv hf' hev
    rw [RothschildStein.S.eLpNorm_top_eq_iSup_of_continuousOn V (huc.mono hV)] at hb
    simpa only [hae] using hb

end RothschildStein.H3
