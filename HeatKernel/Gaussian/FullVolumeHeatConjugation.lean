-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.HorizontalHeatDistanceConjugation
public import HeatKernel.Kernel.GlobalSpatialL2

/-! # Distance conjugation of full-volume horizontal heat operators

The canonical spatial L² isometry preserves scalar representatives and hence
intertwines distance multiplication. The native heat bound transfers to full volume.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- The horizontal heat operator expressed on the full-volume kernel space. -/
def fullVolumeHorizontalHeatOperator {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (t : ℝ) : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin N → ℝ)) :=
  (globalSpatialL2Equiv N).conjStarAlgEquiv
    (horizontalHeatOperator ⊤ (G.horizontalFields hq) t.toNNReal)

/-- Full-volume spatial transport intertwines the concrete distance multipliers. -/
theorem globalSpatialL2Equiv_distanceExponentialMultiplication {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) (a : ℝ) (f : SpatialL2 (N := N) ⊤) :
    globalSpatialL2Equiv N (distanceExponentialMultiplication
      (show Measure (CarnotPoint G hq hqpos hspan) from
        (volume : Measure (Fin N → ℝ)).restrict univ) x y a f) =
    distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan)
      x y a (globalSpatialL2Equiv N f) := by
  apply Lp.ext
  have hm := coeFn_distanceExponentialMultiplication
    (show Measure (CarnotPoint G hq hqpos hspan) from
        (volume : Measure (Fin N → ℝ)).restrict univ) x y a f
  simp only [Measure.restrict_univ] at hm
  filter_upwards [ae_globalSpatialL2Equiv (distanceExponentialMultiplication
    (show Measure (CarnotPoint G hq hqpos hspan) from
        (volume : Measure (Fin N → ℝ)).restrict univ) x y a f), hm,
    coeFn_distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan)
      x y a (globalSpatialL2Equiv N f), ae_globalSpatialL2Equiv f] with z hz hm hz' hf
  change _ = _ at hz hm hz' hf
  exact hz.trans (hm.trans (by rw [hf] at hz'; exact hz'.symm))

/-- The full-volume horizontal heat operator satisfies the concrete distance
conjugation bound without compatibility or differentiability hypotheses. -/
theorem norm_fullVolumeHorizontalHeat_distance_conjugation_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan) x y a).comp
      ((fullVolumeHorizontalHeatOperator G hq t).comp
        (distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan) x y (-a)))‖ ≤
      Real.exp (a ^ 2 * t) := by
  let e := globalSpatialL2Equiv N
  let μ : Measure (CarnotPoint G hq hqpos hspan) :=
    (volume : Measure (Fin N → ℝ)).restrict (univ : Set (Fin N → ℝ))
  let M := fun b ↦ distanceExponentialMultiplication μ x y b
  let H := horizontalHeatOperator ⊤ (G.horizontalFields hq) t.toNNReal
  have hM : ∀ b f, distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan)
      x y b f = e (M b (e.symm f)) := by
    intro b f
    simpa only [e, M, μ, LinearIsometryEquiv.apply_symm_apply] using
      (globalSpatialL2Equiv_distanceExponentialMultiplication G hq hqpos hspan x y b (e.symm f)).symm
  have hn := norm_horizontalHeat_carnot_distance_conjugation_le G hq hqpos hspan x y a ht
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  change ‖distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan) x y a
    (e (H (e.symm (distanceExponentialMultiplication (CarnotPoint.volume G hq hqpos hspan) x y (-a) f))))‖ ≤ _
  rw [hM a, hM (-a), e.symm_apply_apply, e.symm_apply_apply, e.norm_map]
  calc
    ‖M a (H (M (-a) (e.symm f)))‖ ≤
        ‖(M a).comp (H.comp (M (-a)))‖ * ‖e.symm f‖ :=
      ContinuousLinearMap.le_opNorm ((M a).comp (H.comp (M (-a)))) (e.symm f)
    _ ≤ Real.exp (a ^ 2 * t) * ‖f‖ := by
      rw [e.symm.norm_map]
      exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

end HeatKernel.Gaussian
