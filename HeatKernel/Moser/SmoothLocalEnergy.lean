-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import HeatKernel.Form.ParabolicEnergyCurves
public import RothschildStein.S.ClassicalWords

/-!
# Local energy of smooth space-time functions

Smooth functions have locally bounded spatial L² norms and locally square
integrable horizontal gradients. A spacetime test identity therefore suffices
to place a smooth function in the local weak solution class.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Continuous functions are square integrable on compact coordinate sets. -/
theorem memLp_two_on_compact_of_continuous {E : Type*} [TopologicalSpace E] [MeasureSpace E] [BorelSpace E] [T2Space E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {f : E → ℝ} (hf : Continuous f) {K : Set E} (hK : IsCompact K) :
    MemLp f 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

/-- Spatial section differentials agree with the spatial part of the spacetime differential. -/
theorem fderiv_spaceSection_apply {n : ℕ} {u : ℝ × (Fin n → ℝ) → ℝ}
    (hu : Differentiable ℝ u) (t : ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => u (t, y)) x v = fderiv ℝ u (t, x) (0, v) := by
  have hd := (hu (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  simpa [Function.comp_def] using congrArg (fun L => L v) hd.fderiv

/-- A continuous spacetime function has locally bounded spatial L² norms, uniformly in time. -/
theorem essSup_spatial_eLpNorm_lt_top_of_continuous {n : ℕ}
    {u : ℝ × (Fin n → ℝ) → ℝ} (hu : Continuous u)
    {J : Set ℝ} {K : Set (Fin n → ℝ)} (hJ : IsCompact J) (hK : IsCompact K) :
    essSup (fun t => eLpNorm (fun x => u (t, x)) 2 (volume.restrict K))
      (volume.restrict J) < ⊤ := by
  obtain ⟨C, hC⟩ := (hJ.prod hK).exists_bound_of_continuousOn hu.continuousOn
  have hb : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x => u (t, x)) 2 (volume.restrict K) ≤
        volume K ^ (1 / (2 : ℝ)) * ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    have hm : AEStronglyMeasurable (fun x => u (t, x)) (volume.restrict K) :=
      (hu.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hc : ∀ᵐ x ∂volume.restrict K, ‖u (t, x)‖ ≤ C := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hC (t, x) ⟨ht, hx⟩
    simpa using eLpNorm_le_of_ae_bound (p := 2) hm hc
  apply (essSup_le_of_ae_le _ hb).trans_lt
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_lt_top.ne)
    ENNReal.ofReal_lt_top

/-- Smooth spacetime functions have the local energy bounds for their classical horizontal gradient. -/
theorem hasLocalParabolicEnergyBounds_of_contDiff {n q : ℕ}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hX : ∀ i, Continuous (X i))
    {u : ℝ × (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (I : Opens ℝ) (U : Opens (Fin n → ℝ)) :
    HasLocalParabolicEnergyBounds I U (fun t x => u (t, x))
      (fun i t x => fderiv ℝ u (t, x) (0, X i x)) := by
  intro J K hJ _ hK _
  refine ⟨essSup_spatial_eLpNorm_lt_top_of_continuous hu.continuous hJ hK, fun i => ?_⟩
  apply memLp_two_on_compact_of_continuous _ (hJ.prod hK)
  exact (hu.continuous_fderiv (by simp)).clm_apply
    (continuous_const.prodMk ((hX i).comp continuous_snd))

/-- A smooth function satisfying the spacetime identity is a local weak solution. -/
theorem isLocalWeakSolution_of_contDiff_of_testIdentity {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ × (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (htest : SatisfiesParabolicTestIdentity (G.horizontalFields hq) a I U
      (fun t x => u (t, x)) (fun i t x => fderiv ℝ u (t, x) (0, G.horizontalFields hq i x))) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => u (t, x)) := by
  refine ⟨hu.continuous.aestronglyMeasurable, (fun i t x =>
    fderiv ℝ u (t, x) (0, G.horizontalFields hq i x)), ?_, ?_, htest⟩
  · apply ae_of_all
    intro t i
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => u (t, x)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    have hc := S.hasWeakWordDeriv_classical U (G.horizontalFields hq)
      (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) [i] (fun x => u (t, x)) hs.contDiffOn
    have he : wordDerivative (G.horizontalFields hq) [i] (fun x => u (t, x)) =
        (fun x => fderiv ℝ u (t, x) (0, G.horizontalFields hq i x)) := by
      funext x
      exact fderiv_spaceSection_apply (hu.differentiable (by simp)) t x _
    rwa [he] at hc
  · exact hasLocalParabolicEnergyBounds_of_contDiff
      (fun i => (G.horizontalFields_contDiff hq i).continuous) hu I U

end HeatKernel
