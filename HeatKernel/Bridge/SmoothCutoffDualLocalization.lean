-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.BoundedCutoffDualLocalization
public import HeatKernel.Form.LocalEnergyAlgebra
import Mathlib.Tactic.Linter

/-! # Smooth compact cutoffs in dual energy balances -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Every smooth compact spatial cutoff localizes a dual energy pair,
including its complete horizontal product gradient. -/
theorem IsDualEnergyPair.exists_smooth_cutoff_localization {N q : ℕ}
    (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ)))
    {J : Set ℝ} {u : ℝ → (Fin N → ℝ) → ℝ}
    {b : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {D F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    (h : IsDualEnergyPair (E := zeroBoundaryGraph V X) J
      (fun t v => ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
      (fun t v => ∑ i, ∫ x, b i t x * (v : GradientSpace (N := N) ⊤ q).snd i x) D F) :
    ∃ D' F' : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ),
      IsDualEnergyPair (E := energyGraph (N := N) ⊤ X) J
        (fun t v => ∫ x, u t x * (φ x * (v : GradientSpace (N := N) ⊤ q).fst x))
        (fun t v => ∑ i, ∫ x, b i t x *
          (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
            fieldDerivative (X i) φ x * (v : GradientSpace (N := N) ⊤ q).fst x)) D' F' := by
  classical
  have hder (i : Fin q) : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) φ) := by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      S.contDiffOn_fieldDerivative (⊤ : Opens (Fin N → ℝ)) (X i) φ
        (hX i).contDiffOn hφ.contDiffOn
  have hcder (i : Fin q) : HasCompactSupport (fieldDerivative (X i) φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) φ)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  choose B hB using fun i => (hcder i).exists_bound_of_continuous (hder i).continuous
  have hBp (i : Fin q) : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
  have hbs (i : Fin q) : ∀ᵐ x ∂volume, ‖fieldDerivative (X i) φ x‖ ≤ ∑ j, B j :=
    Filter.Eventually.of_forall fun x => (hB i x).trans
      (Finset.single_le_sum (fun j _ => hBp j) (Finset.mem_univ i))
  have hk (i : Fin q) : hasWeakWordDeriv X ⊤ [i] φ (fieldDerivative (X i) φ) :=
    S.hasWeakWordDeriv_classical ⊤ X (fun j => (hX j).contDiffOn) [i] φ hφ.contDiffOn
  exact h.exists_bounded_cutoff_localization V X hX hc hs
    (memLocalEnergy_of_contDiff ⊤ X hX hφ) hk hCp
    (Finset.sum_nonneg (fun i _ => hBp i)) (Filter.Eventually.of_forall hC) hbs

end HeatKernel
