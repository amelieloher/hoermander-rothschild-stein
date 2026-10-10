-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.LocalTruncationRepresentative
public import HeatKernel.Form.LocalWeakDerivatives
public import HeatKernel.Poincare.TruncationMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

/-- Symmetric truncation preserves the local energy domain and has the pointwise
weak horizontal derivative formula on the full open domain. -/
theorem MemLocalEnergy.symmetric_truncation {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    {g : Fin q → (Fin N → ℝ) → ℝ}
    (hfg : ∀ i, hasWeakWordDeriv X U [i] f (g i)) {M : ℝ} (hM : 0 ≤ M) :
    MemLocalEnergy U X (fun x => max (-M) (min (f x) M)) ∧
      ∀ i, hasWeakWordDeriv X U [i] (fun x => max (-M) (min (f x) M))
        (fun x => if |f x| ≤ M then g i x else 0) := by
  constructor
  · refine ⟨aestronglyMeasurable_symmetric_truncation hf.1 M, ?_⟩
    intro V hVc hVU
    obtain ⟨z, hzf, _⟩ := hf.exists_symmetric_truncation_representative U X hX hfg hM V hVc hVU
    exact ⟨z, hzf⟩
  · intro i
    apply hasWeakWordDeriv_of_precompact_restrictions U X [i]
    intro V hVc hVU
    obtain ⟨z, hzf, hzg⟩ := hf.exists_symmetric_truncation_representative U X hX hfg hM V hVc hVU
    have hw := energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) z.property i
    exact S.hasWeakWordDeriv_congr_ae X V
      (S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) hw) hzf (hzg i)

end HeatKernel
