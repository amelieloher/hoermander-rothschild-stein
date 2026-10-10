-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoreGradientGraph

/-!
# Smooth approximation in the graph norm

Componentwise L² approximation by smooth compactly supported functions places a
function-gradient pair in the energy graph.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

/-- L² convergence of representatives is convergence of their quotient classes. -/
theorem tendsto_L2_of_representatives {α β : Type*} [MeasurableSpace β]
    {μ : Measure β} {l : Filter α} {U : α → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    {f : α → β → ℝ} {g : β → ℝ}
    (hU : ∀ a, U a =ᵐ[μ] f a) (hv : v =ᵐ[μ] g)
    (hlim : Tendsto (fun a => eLpNorm (f a - g) 2 μ) l (𝓝 0)) :
    Tendsto U l (𝓝 v) := by
  apply tendsto_iff_edist_tendsto_0.mpr
  apply hlim.congr
  intro a
  rw [Lp.edist_def]
  exact (eLpNorm_congr_ae ((hU a).sub hv)).symm

/-- A componentwise L² limit of smooth gradient pairs belongs to the closed energy graph. -/
theorem mem_energyGraph_of_smooth_approximation {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : GradientSpace (N := N) ⊤ q) {f : ℕ → (Fin N → ℝ) → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hfun : Tendsto (fun n => eLpNorm (f n - ⇑v.fst) 2 volume) atTop (𝓝 0))
    (hgrad : ∀ i, Tendsto (fun n => eLpNorm
      (RothschildStein.fieldDerivative (X i) (f n) - ⇑(v.snd i)) 2 volume) atTop (𝓝 0)) :
    v ∈ energyGraph ⊤ X := by
  choose w hw hwf using fun n => exists_smoothGradientPair X (hf n) (hc n) hX
  have hwf' : ∀ n, (w n).fst =ᵐ[volume.restrict (⊤ : Opens (Fin N → ℝ))] f n := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hwf
  have hwg : ∀ n i, (w n).snd i =ᵐ[volume.restrict (⊤ : Opens (Fin N → ℝ))]
      RothschildStein.fieldDerivative (X i) (f n) := by
    intro n i
    have hwk := smoothGradientSpan_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn)
      (Submodule.subset_span (hw n)) i
    have hck := RothschildStein.S.hasWeakWordDeriv_classical ⊤ X
      (fun j => (hX j).contDiffOn) [i] (f n) (hf n).contDiffOn
    have hck' := RothschildStein.S.hasWeakWordDeriv_congr_ae X ⊤ hck
      (hwf' n).symm Filter.EventuallyEq.rfl
    exact RothschildStein.S.hasWeakWordDeriv_unique X ⊤ hwk hck'
  have ht : Tendsto (fun n => (w n).fst) atTop (𝓝 v.fst) := by
    apply tendsto_L2_of_representatives hwf' Filter.EventuallyEq.rfl
    simpa only [Opens.coe_top, Measure.restrict_univ] using hfun
  have hd : ∀ i, Tendsto (fun n => (w n).snd i) atTop (𝓝 (v.snd i)) := by
    intro i
    apply tendsto_L2_of_representatives (fun n => hwg n i) Filter.EventuallyEq.rfl
    simpa only [Opens.coe_top, Measure.restrict_univ] using hgrad i
  have hp := ((PiLp.continuous_toLp 2
    (fun _ : Fin q => SpatialL2 (⊤ : Opens (Fin N → ℝ)))).tendsto _).comp
      (tendsto_pi_nhds.mpr hd)
  have he := (((WithLp.homeomorphProd 2 (SpatialL2 (⊤ : Opens (Fin N → ℝ)))
    (PiLp 2 (fun _ : Fin q => SpatialL2 (⊤ : Opens (Fin N → ℝ))))).symm.continuous).tendsto _).comp
      (ht.prodMk_nhds hp)
  apply (isClosed_energyGraph ⊤ X).mem_of_tendsto he
  exact Filter.Eventually.of_forall fun n =>
    smoothGradientSpan_le_energyGraph ⊤ X (Submodule.subset_span (hw n))

end HeatKernel
