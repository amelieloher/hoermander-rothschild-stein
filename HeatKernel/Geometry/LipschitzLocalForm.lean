-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.LipschitzSobolev
public import HeatKernel.Geometry.LocalLipschitzEnergy
public import HeatKernel.Form.LocalEnergyIdentification

/-! Local form membership and sharp weak gradients of horizontal Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
open scoped NNReal ENNReal BigOperators
namespace HeatKernel

/-- Horizontal metric Lipschitz functions belong to the local closed form domain. -/
theorem CarnotPoint.memLocalEnergy_of_lipschitz {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    MemLocalEnergy ⊤ (G.horizontalFields hq) f := by
  have hfc : Continuous (show (Fin N → ℝ) → ℝ from f) := hf.continuous
  have hm : AEStronglyMeasurable (show (Fin N → ℝ) → ℝ from f)
      ((MeasureTheory.volume : Measure (Fin N → ℝ)).restrict (⊤ : Opens (Fin N → ℝ))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (hfc.aestronglyMeasurable (μ := (MeasureTheory.volume : Measure (Fin N → ℝ))))
  apply memLocalEnergy_of_memSobolevXLoc ⊤ (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) hm
  exact memSobolevXLoc_of_lipschitz G hq hqpos hspan hf

/-- Local form membership and the joint weak gradient bound hold for the same function. -/
theorem CarnotPoint.exists_local_form_gradient {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    MemLocalEnergy ⊤ (G.horizontalFields hq) f ∧
      ∃ g : Fin q → (Fin N → ℝ) → ℝ,
        (∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f (g i)) ∧
        (∀ᵐ x ∂(MeasureTheory.volume : Measure (Fin N → ℝ)),
          Real.sqrt (∑ i, (g i x)^2) ≤ L) ∧
        ∀ (V : Opens (Fin N → ℝ)) (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)),
          energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[MeasureTheory.volume.restrict (V : Set (Fin N → ℝ))] f →
          ∀ i, energyGradient ⊤ (G.horizontalFields hq) u i =ᵐ[MeasureTheory.volume.restrict (V : Set (Fin N → ℝ))] g i := by
  obtain ⟨g, hg, hb⟩ := exists_weak_horizontal_gradient G hq hqpos hspan hf
  refine ⟨memLocalEnergy_of_lipschitz G hq hqpos hspan hf, g, hg, hb, ?_⟩
  intro V u hu
  exact energyGradient_eq_weak_derivative_locally (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) u V hu g
    (fun i => S.hasWeakWordDeriv_restrict (G.horizontalFields hq) ⊤ V (subset_univ _) (hg i))

end HeatKernel
