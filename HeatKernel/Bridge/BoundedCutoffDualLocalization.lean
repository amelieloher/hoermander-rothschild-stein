-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompactDualLocalization
import Mathlib.Tactic.Linter

/-! # Bounded local cutoffs in dual energy balances -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A compact local energy cutoff with bounded value and horizontal derivatives
localizes a dual energy pair with its complete Leibniz flux. -/
theorem IsDualEnergyPair.exists_bounded_cutoff_localization {N q : ℕ}
    (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ)))
    (hloc : MemLocalEnergy ⊤ X φ)
    (hk : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (k i))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ C)
    (hkb : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ L)
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
  obtain ⟨M, hM⟩ := exists_energyMultiplierLinearMap X hX hloc hk hC hL hb hkb
  exact h.exists_compact_localization V X hX hc hs M
    (fun v => (hM v).1) (fun v i => (hM v).2 i)

end HeatKernel
