-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualEnergyPrecomposition
public import HeatKernel.Form.CompactEnergyMultipliers
import Mathlib.Tactic.Linter

/-! # Compact spatial localization of dual energy balances -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A compact energy multiplier localizes a dual energy pair. Its flux
contains the complete horizontal Leibniz expression. -/
theorem IsDualEnergyPair.exists_compact_localization {N q : ℕ}
    (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ)))
    (M : energyGraph (N := N) ⊤ X →L[ℝ] energyGraph (N := N) ⊤ X)
    (hM : ∀ v, (M v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => φ x * (v : GradientSpace (N := N) ⊤ q).fst x)
    (hMk : ∀ v i, (M v : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (v : GradientSpace (N := N) ⊤ q).fst x)
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
            k i x * (v : GradientSpace (N := N) ⊤ q).fst x)) D' F' := by
  let A := compactEnergyMultiplier V X hX hc hs M hM
  obtain ⟨hD, hF, hDr, hFr, ht⟩ := h.precompose A
  refine ⟨fun t => dualPrecomposition A (D t), fun t => dualPrecomposition A (F t),
    hD, hF, ?_, ?_, ht⟩
  · filter_upwards [hDr] with t ht
    intro v
    rw [ht v]
    apply integral_congr_ae
    filter_upwards [hM v] with x hx
    change u t x * (M v : GradientSpace (N := N) ⊤ q).fst x = _
    rw [hx]
  · filter_upwards [hFr] with t ht
    intro v
    rw [ht v]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hMk v i] with x hx
    change b i t x * (M v : GradientSpace (N := N) ⊤ q).snd i x = _
    rw [hx]

end HeatKernel
