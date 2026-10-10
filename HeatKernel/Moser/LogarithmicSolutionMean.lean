-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicSolutionCutoff
public import HeatKernel.Moser.LogarithmicTentMeanCorrection
public import HeatKernel.Bridge.ParabolicCoefficientBounds
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Corrected logarithmic tent means supplied by local weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A nonnegative weak solution supplies an absolutely continuous shifted-log
mean with a monotone correction uniform in the positive shift. The energy uses
the original compatible weak gradient, and the tent mass is literal. -/
theorem IsLocalWeakSolution.exists_logarithmic_tent_mean {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (hu0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂volume.restrict ((I : Set ℝ) ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)),
        0 ≤ u z.1 z.2)
    {A B : ℝ} (hJ : Icc A B ⊆ (I : Set ℝ))
    {a b c : ℝ} (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    (hc : 0 < c) (hupper : 0 ≤ upper) :
    let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
      isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal /
      (3 * r / 2)) 0
    let D := upper * (((G.homogeneousDimension : ℝ) + 1) *
      ((G.homogeneousDimension : ℝ) + 2)) / (3 * r / 2)^2
    ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      WeakSolutionEnergyInterface (G.horizontalFields hq) coeff I U u g ∧
      ∃ m : ℝ → ℝ, AbsolutelyContinuousOnInterval m a b ∧
      m =ᵐ[volume.restrict (Icc a b)] (fun t => (∫ y, η y^2)⁻¹ *
        ∫ y, η y^2 * (Real.log (u t y + c) - Real.log c)) ∧
      AbsolutelyContinuousOnInterval (fun t => m t + D * t) a b ∧
      MonotoneOn (fun t => m t + D * t) (Icc a b) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b),
        ((∫ y, η y^2)⁻¹ * ∫ y, ∑ i, ∑ j, coeff t y i j *
          (η y * ((u t y + c)⁻¹ * g j t y)) *
          (η y * ((u t y + c)⁻¹ * g i t y))) ≤
            2 * deriv (fun s => m s + D * s) t := by
  obtain ⟨φ, d, W, w, g, v, F, hg, hp, hz, hW, hD, hwv, hwd, hd, hzero, hplateau⟩ :=
    hu.exists_logarithmic_tent_cutoff_pair G hq hqpos hspan hw x hr coeff I ha hlower hbound hu0 hJ
  have hentries : ∀ᵐ t ∂volume, ∀ i j, ∀ᵐ y ∂volume, ‖coeff t y i j‖ ≤ upper :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => Measure.ae_ae_of_ae_prod (by
      simpa only [Measure.restrict_univ, Measure.volume_eq_prod] using
        ae_norm_parabolic_coefficient_entry_le coeff hlower hbound univ i j)
  have hslices := ae_restrict_of_ae (s := Icc A B) (Measure.ae_ae_of_ae_prod hbound)
  have hquad : ∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ y ∂volume, ∀ ξ : Fin q → ℝ,
      lower * coordinateNormSq ξ ≤ matrixEnergy (coeff t y) ξ ∧
      matrixEnergy (coeff t y) ξ ≤ upper * coordinateNormSq ξ := by
    filter_upwards [hslices] with t ht
    filter_upwards [ht] with y hy ξ
    simpa only [matrixEnergy, coordinateNormSq, mul_assoc, mul_left_comm, mul_comm]
      using hy.2 ξ
  have hcoeff : ∀ᵐ t ∂volume.restrict (Icc A B),
      (∀ i j, AEStronglyMeasurable (fun y => coeff t y i j) volume) ∧
      (∀ i j, ∀ᵐ y ∂volume, ‖coeff t y i j‖ ≤ upper) ∧
      (∀ᵐ y ∂volume, ∀ i j, coeff t y i j = coeff t y j i) ∧
      (∀ᵐ y ∂volume, ∀ ξ, 0 ≤ matrixEnergy (coeff t y) ξ) := by
    filter_upwards [hslices, hquad, ae_restrict_of_ae hentries] with t ht hqf hb
    refine ⟨fun i j => ((ha i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
      hb, ht.mono (fun y hy => hy.1), ?_⟩
    filter_upwards [hqf] with y hy ξ
    exact (mul_nonneg hlower (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i))).trans (hy ξ).1
  have hgrad : ∀ᵐ y ∂volume, y ∈ horizontalBall (G.horizontalFields hq) x (3 * r / 2) →
      coordinateNormSq (fun i => (d : GradientSpace (N := N) ⊤ q).snd i y) ≤
        ((3 * r / 2)^2)⁻¹ := hd.mono fun y hy _ => hy
  obtain ⟨m, hm, hmean, hcorr, hmono, henergy⟩ :=
    hp.exists_corrected_logarithmic_tent_mean G hq hqpos hspan hw x
      (by positivity : 0 < 3 * r / 2) hupper W w hwv hwd hplateau hz rfl hgrad hzero
      (Filter.Eventually.of_forall fun y => congrFun hW y)
      (fun i => Filter.Eventually.of_forall fun y => congrFun (congrFun hD i) y)
      (fun i => by
        simpa only [Opens.coe_top, Measure.restrict_univ] using
          (Lp.memLp ((d : GradientSpace (N := N) ⊤ q).snd i))) hcoeff
      (hquad.mono fun t ht => ht.mono fun y hy ξ => (hy ξ).2) hc hab hAa hbB
  refine ⟨g, hg, m, hm, ?_, hcorr, hmono, ?_⟩
  · simpa only [hW] using hmean
  · simpa only [hW] using henergy

end HeatKernel
