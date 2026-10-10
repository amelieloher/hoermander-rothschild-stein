-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ConvolutionLipschitz
public import RothschildStein.G2.MollifierLpConvergence
public import RothschildStein.G2.MollifierSmooth

/-! Smooth horizontal Lipschitz regularizations and their closed form representatives. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter
open scoped NNReal ENNReal BigOperators Topology
namespace HeatKernel

/-- Positive-scale group regularization preserves the horizontal Lipschitz constant. -/
theorem CarnotPoint.lipschitzWith_groupRegularize {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith (α := CarnotPoint G hq hqpos hspan) L (G2.groupRegularize G φ f ε) := by
  exact lipschitzWith_groupConvolution G hq hqpos hspan
    (G2.contDiff_groupMollifierScale G φ ε).continuous
    (G2.hasCompactSupport_groupMollifierScale G φ hε)
    (G2.groupMollifierScale_nonneg G φ hε) (G2.integral_groupMollifierScale G φ hε) hf

/-- Compact horizontal Lipschitz regularizations are smooth compact form functions,
with their original sharp gradient bound. -/
theorem CarnotPoint.groupRegularize_compact_form {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (G2.groupRegularize G φ f ε) ∧
      HasCompactSupport (G2.groupRegularize G φ f ε) ∧
      ∃ u : energyGraph (N := N) ⊤ (G.horizontalFields hq),
        energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[MeasureTheory.volume] G2.groupRegularize G φ f ε ∧
        ∀ᵐ x ∂MeasureTheory.volume,
          Real.sqrt (∑ i, (energyGradient ⊤ (G.horizontalFields hq) u i x)^2) ≤ L := by
  have hfc : Continuous (show (Fin N → ℝ) → ℝ from f) := hf.continuous
  have hs := G2.contDiff_groupRegularize G φ hε (p := 2) (by norm_num) (hfc.memLp_of_hasCompactSupport hc)
  have hcs := G2.hasCompactSupport_groupRegularize G φ hε hc
  exact ⟨hs, hcs, exists_energyGraph_of_compact_lipschitz G hq hqpos hspan
    (lipschitzWith_groupRegularize G hq hqpos hspan φ hε hf) hcs⟩

end HeatKernel
