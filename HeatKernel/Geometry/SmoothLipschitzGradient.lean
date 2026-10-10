-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.LipschitzRegularization
public import HeatKernel.Geometry.SmoothBallCutoff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Pointwise horizontal gradient bounds for smooth horizontal Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
open scoped NNReal ENNReal BigOperators
namespace HeatKernel

/-- For smooth horizontal metric Lipschitz functions, the sharp joint weak gradient
bound is a pointwise bound on the classical horizontal gradient. -/
theorem CarnotPoint.horizontalGradientNorm_le_of_smooth_lipschitz {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (show (Fin N → ℝ) → ℝ from f)) (hl : LipschitzWith L f) :
    ∀ x, horizontalGradientNorm (G.horizontalFields hq) f x ≤ L := by
  obtain ⟨g, hg, hb⟩ := exists_weak_horizontal_gradient G hq hqpos hspan hl
  unfold CarnotPoint at *
  have he : ∀ i, g i =ᵐ[(MeasureTheory.volume : Measure (Fin N → ℝ))]
      fieldDerivative (G.horizontalFields hq i) f := by
    intro i
    have hc := S.hasWeakWordDeriv_classical ⊤ (G.horizontalFields hq)
      (fun j => (G.horizontalFields_contDiff hq j).contDiffOn) [i] f hf.contDiffOn
    simpa only [Opens.coe_top, Measure.restrict_univ, wordDerivative] using
      S.hasWeakWordDeriv_unique (G.horizontalFields hq) ⊤ (hg i) hc
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume : Measure (Fin N → ℝ)),
      horizontalGradientNorm (G.horizontalFields hq) f x ≤ L := by
    filter_upwards [ae_all_iff.mpr he, hb] with x hx hbx
    change Real.sqrt (∑ i, (fieldDerivative (G.horizontalFields hq i) f x)^2) ≤ L
    simpa only [hx] using hbx
  have hD := hf.continuous_fderiv (by simp)
  have hcont : Continuous (horizontalGradientNorm (G.horizontalFields hq) f) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ (fun i _ =>
      (hD.clm_apply (G.horizontalFields_contDiff hq i).continuous).pow 2))
  have heq := Measure.eq_of_ae_eq (hbound.mono fun _ hx => min_eq_left hx)
    (hcont.min continuous_const) hcont
  intro x
  rw [← congrFun heq x]
  exact min_le_right _ _

/-- Smooth group regularization preserves the sharp classical joint gradient bound
at every point, for every positive scale. -/
theorem CarnotPoint.horizontalGradientNorm_groupRegularize_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    ∀ x, horizontalGradientNorm (G.horizontalFields hq) (G2.groupRegularize G φ f ε) x ≤ L := by
  have hfc : Continuous (show (Fin N → ℝ) → ℝ from f) := hf.continuous
  have hs := G2.contDiff_groupConvolution_left G (G2.contDiff_groupMollifierScale G φ ε)
    (G2.hasCompactSupport_groupMollifierScale G φ hε) hfc.locallyIntegrable
  exact horizontalGradientNorm_le_of_smooth_lipschitz G hq hqpos hspan hs
    (lipschitzWith_groupRegularize G hq hqpos hspan φ hε hf)

end HeatKernel
