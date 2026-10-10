-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.EnergySymmetricTruncation
public import HeatKernel.Form.LocalEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

/-- On each compact interior patch, symmetric truncation of a local energy function
has a global energy representative with the explicit restricted-gradient formula. -/
theorem MemLocalEnergy.exists_symmetric_truncation_representative {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    {g : Fin q → (Fin N → ℝ) → ℝ}
    (hfg : ∀ i, hasWeakWordDeriv X U [i] f (g i))
    {M : ℝ} (hM : 0 ≤ M) (V : Opens (Fin N → ℝ))
    (hVc : IsCompact (closure (V : Set (Fin N → ℝ))))
    (hVU : closure (V : Set (Fin N → ℝ)) ⊆ U) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
        (fun x => max (-M) (min (f x) M)) ∧
      ∀ i, energyGradient ⊤ X z i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
        (fun x => if |f x| ≤ M then g i x else 0) := by
  obtain ⟨u, hu⟩ := hf.2 V hVc hVU
  change energyInclusion ⊤ X u =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f at hu
  have hgu : ∀ i, energyGradient ⊤ X u i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i := by
    intro i
    have hw := energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) u.property i
    have hr := S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) hw
    have hc := S.hasWeakWordDeriv_congr_ae X V hr hu EventuallyEq.rfl
    exact S.hasWeakWordDeriv_unique X V hc
      (S.hasWeakWordDeriv_restrict X U V (subset_closure.trans hVU) (hfg i))
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_symmetric_truncation X hX u hM
  refine ⟨z, ?_, fun i => ?_⟩
  · have hz := hzf.filter_mono (ae_mono (Measure.restrict_le_self :
        volume.restrict (V : Set (Fin N → ℝ)) ≤ volume))
    exact hz.trans (hu.fun_comp (fun t => max (-M) (min t M)))
  · have hz := (hzg i).filter_mono (ae_mono (Measure.restrict_le_self :
        volume.restrict (V : Set (Fin N → ℝ)) ≤ volume))
    filter_upwards [hz, hu, hgu i] with x hx hux hgx
    simp only [energyInclusion_apply, energyGradient_apply] at hux hgx ⊢
    rwa [hux, hgx] at hx

end HeatKernel
