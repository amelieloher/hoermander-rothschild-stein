-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalEssentialSupport
public import HeatKernel.Moser.WeakSolutionSpatialWeights

/-! # Fixed form-domain representatives of compact spatial weights

Compactly supported local energy weights give zero-boundary spatial tests.
Uniqueness of weak horizontal derivatives identifies their gradient coordinates.
These fixed tests restore the constant derivative terms in centered nonlinear tests.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
namespace HeatKernel

/-- A compactly supported local energy weight and its weak horizontal derivatives
have a representative in the stated zero-boundary form domain. -/
theorem exists_compact_spatial_energy_test {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {ψ : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy ⊤ X ψ) (hd : ∀ i, hasWeakWordDeriv X ⊤ [i] ψ (d i))
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (V : Set (Fin N → ℝ))) :
    ∃ w : zeroBoundaryGraph V X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] ψ ∧
      ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] d i := by
  have hz : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)),
      x ∉ tsupport ψ → ψ x = 0 := by
    exact Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨z, _, hval⟩ := hψ.exists_zeroBoundaryGraph_extension ⊤ X hX hc (subset_univ _) hz
  have hv : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] ψ := by
    simpa only [Opens.coe_top, indicator_univ] using hval
  have hzero : (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph V X :=
    mem_zeroBoundaryGraph_of_compact_multiplier V X hX z hc hs
      (by simpa only [mul_one] using hv :
        (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => ψ x * (1 : ℝ))
  refine ⟨⟨z, hzero⟩, hv, fun i => ?_⟩
  have hder := energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) z.property i
  have hv' : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[
      volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))] ψ := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hv
  have hunique := S.hasWeakWordDeriv_unique X ⊤
    (S.hasWeakWordDeriv_congr_ae X ⊤ hder hv' EventuallyEq.rfl) (hd i)
  simpa only [Opens.coe_top, Measure.restrict_univ] using hunique

end HeatKernel
